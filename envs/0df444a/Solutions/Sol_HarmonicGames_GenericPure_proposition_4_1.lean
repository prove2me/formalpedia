-- Prove2me | solution 1 for HarmonicGames.GenericPure.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T06:48:48.490583+00:00
-- url     : https://prove2.me/submissions/dc699904-e5cd-4cb8-96b5-9a7875ba523b

import Mathlib
import Definitions.Def_HarmonicGames_GenericPure_Games

/- Supporting proof: Nickrobbins95, accepted submission 8370ef64-33e8-4a29-a1ac-bda9f692f938. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Pbccb4299

open HarmonicGames.Decomposition
open scoped InnerProductSpace

section Pinv
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]

lemma sub_proj_mem_ker (L : V →ₗ[ℝ] W) (x : V) :
    x - (LinearMap.ker L)ᗮ.starProjection x ∈ LinearMap.ker L := by
  have := (LinearMap.ker L)ᗮ.sub_starProjection_mem_orthogonal x
  rwa [Submodule.orthogonal_orthogonal] at this

lemma map_proj (L : V →ₗ[ℝ] W) (x : V) :
    L ((LinearMap.ker L)ᗮ.starProjection x) = L x := by
  have h1 := sub_proj_mem_ker L x
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
  exact h1.symm

lemma pinv_apply_self (L : V →ₗ[ℝ] W) (x : V) :
    pinv L (L x) = (LinearMap.ker L)ᗮ.starProjection x := by
  set K := (LinearMap.ker L)ᗮ with hK
  set f := L ∘ₗ K.subtype with hf
  set y : K := K.orthogonalProjectionOnto x with hy
  have hk : L x = f y := by
    rw [← map_proj L x, Submodule.starProjection_apply]; rfl
  have hr : (LinearMap.range f).orthogonalProjectionOnto (f y) =
      ⟨f y, LinearMap.mem_range_self f y⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨f y, LinearMap.mem_range_self f y⟩
  have he : (LinearEquiv.ofInjective f (pinv_restrict_injective L)).symm
      ⟨f y, LinearMap.mem_range_self f y⟩ = y := by
    rw [LinearEquiv.symm_apply_eq]; ext; simp
  unfold pinv
  rw [hk]
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [hr]
  have := congrArg K.subtype he
  exact this.trans (by rw [Submodule.starProjection_apply]; rfl)

lemma map_pinv (L : V →ₗ[ℝ] W) (x : V) : L (pinv L (L x)) = L x := by
  rw [pinv_apply_self, map_proj]

lemma map_pinv_of_mem (L : V →ₗ[ℝ] W) (y : W) (hy : y ∈ LinearMap.range L) :
    L (pinv L y) = y := by
  obtain ⟨x, rfl⟩ := hy
  exact map_pinv L x

lemma pinv_mem (L : V →ₗ[ℝ] W) (y : W) : pinv L y ∈ (LinearMap.ker L)ᗮ := by
  unfold pinv
  simp only [LinearMap.comp_apply]
  exact Submodule.coe_mem _

lemma pinv_map_of_mem (L : V →ₗ[ℝ] W) (v : V) (hv : v ∈ (LinearMap.ker L)ᗮ) :
    pinv L (L v) = v := by
  rw [pinv_apply_self]
  exact (Submodule.starProjection_eq_self_iff).2 hv

lemma map_pinv_eq_proj (L : V →ₗ[ℝ] W) (y : W) :
    L (pinv L y) =
      (LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype)).starProjection y := by
  rw [Submodule.starProjection_apply]
  unfold pinv
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, Submodule.coe_subtype]
  set e := LinearEquiv.ofInjective _ (pinv_restrict_injective L)
  set z := (LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype)).orthogonalProjectionOnto y
  have h1 : (e (e.symm z) : W) = (z : W) := by rw [LinearEquiv.apply_symm_apply]
  rw [← h1, LinearEquiv.ofInjective_apply]
  rfl

lemma inner_map_sub_pinv (L : V →ₗ[ℝ] W) (y : W) (φ : V) :
    ⟪L φ, y - L (pinv L y)⟫_ℝ = 0 := by
  set R := LinearMap.range (L ∘ₗ (LinearMap.ker L)ᗮ.subtype)
  have hmem : L φ ∈ R := by
    rw [← map_proj L φ]
    exact ⟨⟨_, Submodule.starProjection_apply_mem _ _⟩, rfl⟩
  rw [map_pinv_eq_proj]
  exact Submodule.inner_right_of_mem_orthogonal hmem (R.sub_starProjection_mem_orthogonal y)

end Pinv

section Graph
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma C1_sum_apply {α : Type*} (s : Finset α) (f : α → C1 G) (a b : V) :
    (∑ m ∈ s, f m) a b = ∑ m ∈ s, f m a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, C1.add_apply, ih]

lemma adjoint_sub_pinv (X : C1 G) :
    LinearMap.adjoint (delta0 G) (X - delta0 G (pinv (delta0 G) X)) = 0 := by
  refine ext_inner_left ℝ fun φ => ?_
  rw [LinearMap.adjoint_inner_right, inner_map_sub_pinv, inner_zero_right]

lemma range_inter_ker_adjoint (X Y : C1 G) (hX : X ∈ LinearMap.range (delta0 G))
    (hY : Y ∈ LinearMap.ker (LinearMap.adjoint (delta0 G))) (h : X + Y = 0) : X = 0 := by
  obtain ⟨φ, rfl⟩ := hX
  have hY' : Y = -delta0 G φ := eq_neg_of_add_eq_zero_right h
  have : ⟪delta0 G φ, delta0 G φ⟫_ℝ = 0 := by
    have h2 : ⟪delta0 G φ, Y⟫_ℝ = 0 := by
      rw [← LinearMap.adjoint_inner_right, LinearMap.mem_ker.1 hY, inner_zero_right]
    rw [hY', inner_neg_right, neg_eq_zero] at h2
    exact h2
  exact inner_self_eq_zero.1 this

end Graph

section Games
variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

lemma Dop_apply (u : Games E) (a b : ∀ k, E k) :
    (Dop E u) a b = ∑ m, (if MComparable E m a b then (1:ℝ) else 0) * (u m b - u m a) := by
  show (∑ m, Dm E m (u m)) a b = _
  rw [C1_sum_apply]
  rfl

lemma Dm_apply (m : ι) (f : Util E) (a b : ∀ k, E k) :
    (Dm E m f) a b = (if MComparable E m a b then (1:ℝ) else 0) * (f b - f a) := rfl

lemma mcomp_unique {m k : ι} {a b : ∀ j, E j} (hm : MComparable E m a b)
    (hk : MComparable E k a b) : k = m := by
  by_contra hne
  apply hm.1
  funext j
  by_cases hj : j = m
  · subst hj; exact hk.2 j (Ne.symm hne)
  · exact hm.2 j hj

lemma Dop_single (m : ι) (u : Games E) (a b : ∀ k, E k) (h : MComparable E m a b) :
    (Dop E u) a b = (Dm E m (u m)) a b := by
  rw [Dop_apply, Dm_apply]
  refine Finset.sum_eq_single m (fun k _ hk => ?_) (fun h' => absurd (Finset.mem_univ m) h')
  rw [if_neg (fun hk' => hk (mcomp_unique E h hk')), zero_mul]

lemma delta0_mem_range (φ : Util E) :
    delta0 (gameGraph E) φ ∈ LinearMap.range (Dop E) := by
  refine ⟨WithLp.toLp 2 (fun _ => φ), ?_⟩
  ext a b
  rw [Dop_apply]
  show _ = (if (gameGraph E).Adj a b then (1:ℝ) else 0) * (φ b - φ a)
  by_cases h : ∃ m, MComparable E m a b
  · obtain ⟨m, hm⟩ := h
    have hadj : (gameGraph E).Adj a b := ⟨m, hm⟩
    rw [if_pos hadj, Finset.sum_eq_single m]
    · rw [if_pos hm]
    · intro k _ hk
      rw [if_neg (fun hk' => hk (mcomp_unique E hm hk')), zero_mul]
    · intro h'; exact absurd (Finset.mem_univ m) h'
  · have hadj : ¬ (gameGraph E).Adj a b := h
    rw [if_neg hadj, zero_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (fun hk => h ⟨k, hk⟩), zero_mul]

lemma comp_mem_orth (v : Games E) (hv : v ∈ (LinearMap.ker (Dop E))ᗮ) (m : ι) :
    v m ∈ (LinearMap.ker (Dm E m))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  have hmem : (WithLp.toLp 2 (Pi.single m w) : Games E) ∈ LinearMap.ker (Dop E) := by
    rw [LinearMap.mem_ker]
    show ∑ k, Dm E k ((Pi.single m w : ∀ _ : ι, Util E) k) = 0
    rw [Finset.sum_eq_single m]
    · simpa using hw
    · intro k _ hk; simp [Pi.single_eq_of_ne hk]
    · intro h'; exact absurd (Finset.mem_univ m) h'
  have h0 := (Submodule.mem_orthogonal _ _).1 hv _ hmem
  rw [PiLp.inner_apply, Finset.sum_eq_single m] at h0
  · simpa using h0
  · intro k _ hk; simp [Pi.single_eq_of_ne hk]
  · intro h'; exact absurd (Finset.mem_univ m) h'

lemma PiOp_fix (v : Games E) (hv : v ∈ (LinearMap.ker (Dop E))ᗮ) : PiOp E v = v := by
  refine PiLp.ext fun m => ?_
  show pinv (Dm E m) (Dm E m (v m)) = v m
  exact pinv_map_of_mem _ _ (comp_mem_orth E v hv m)

lemma eq_zero_of_fix_ker (v : Games E) (hfix : PiOp E v = v) (hD : Dop E v = 0) : v = 0 := by
  refine PiLp.ext fun m => ?_
  have hm : Dm E m (v m) = 0 := by
    ext a b
    by_cases h : MComparable E m a b
    · rw [← Dop_single E m v a b h, hD]
    · rw [Dm_apply, if_neg h, zero_mul]; rfl
  have : (PiOp E v) m = pinv (Dm E m) (Dm E m (v m)) := rfl
  rw [← hfix, this, hm, map_zero]
  rfl

end Games
end Pbccb4299

/- Supporting proof: Nickrobbins95, accepted submission 8370ef64-33e8-4a29-a1ac-bda9f692f938. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Pbccb4299
open HarmonicGames.Decomposition
open scoped InnerProductSpace
section Games
variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)]
lemma uniq (p h n : Games E) (hp : p ∈ potentialSubspace E) (hh : h ∈ harmonicSubspace E)
    (hn : n ∈ nonstrategicSubspace E) (hs : p + h + n = 0) : p = 0 ∧ h = 0 ∧ n = 0 := by
  have hpD : Dop E p ∈ LinearMap.range (delta0 (gameGraph E)) := Submodule.mem_comap.1 hp.2
  have hhD : Dop E h ∈ LinearMap.ker (LinearMap.adjoint (delta0 (gameGraph E))) :=
    Submodule.mem_comap.1 hh.2
  have hnD : Dop E n = 0 := LinearMap.mem_ker.1 hn
  have hsum : Dop E p + Dop E h = 0 := by
    have := congrArg (Dop E) hs
    rwa [map_add, map_add, hnD, add_zero, map_zero] at this
  have hp0 : Dop E p = 0 := range_inter_ker_adjoint _ _ _ hpD hhD hsum
  have hh0 : Dop E h = 0 := by rw [hp0, zero_add] at hsum; exact hsum
  have hpfix : PiOp E p = p := ((LinearMap.mem_eqLocus).1 hp.1).symm
  have hhfix : PiOp E h = h := ((LinearMap.mem_eqLocus).1 hh.1).symm
  have e1 := eq_zero_of_fix_ker E p hpfix hp0
  have e2 := eq_zero_of_fix_ker E h hhfix hh0
  refine ⟨e1, e2, ?_⟩
  rw [e1, e2, zero_add, zero_add] at hs
  exact hs

lemma part3 (u : Games E) :
    Dop E (potentialComponent E u) = delta0 (gameGraph E) (potentialFunction E u) := by
  show Dop E (pinv (Dop E) (delta0 (gameGraph E) (pinv (delta0 (gameGraph E)) (Dop E u)))) = _
  exact map_pinv_of_mem _ _ (delta0_mem_range E _)

lemma part2 (u : Games E) :
    potentialComponent E u + harmonicComponent E u + nonstrategicComponent E u = u ∧
    potentialComponent E u ∈ potentialSubspace E ∧
    harmonicComponent E u ∈ harmonicSubspace E ∧
    nonstrategicComponent E u ∈ nonstrategicSubspace E := by
  set x := Dop E u with hx
  set y := delta0 (gameGraph E) (pinv (delta0 (gameGraph E)) x) with hy
  have hP : potentialComponent E u = pinv (Dop E) y := rfl
  have hH : harmonicComponent E u = pinv (Dop E) (x - y) := rfl
  have hN : nonstrategicComponent E u = u - pinv (Dop E) x := rfl
  have hyR : y ∈ LinearMap.range (Dop E) := delta0_mem_range E _
  have hxyR : x - y ∈ LinearMap.range (Dop E) :=
    Submodule.sub_mem _ (LinearMap.mem_range_self _ u) hyR
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hP, hH, hN, map_sub]; abel
  · rw [hP]
    refine ⟨(LinearMap.mem_eqLocus).2 (PiOp_fix E _ (pinv_mem _ _)).symm, ?_⟩
    change Dop E (pinv (Dop E) y) ∈ LinearMap.range (delta0 (gameGraph E))
    rw [map_pinv_of_mem _ _ hyR]
    exact LinearMap.mem_range_self _ _
  · rw [hH]
    refine ⟨(LinearMap.mem_eqLocus).2 (PiOp_fix E _ (pinv_mem _ _)).symm, ?_⟩
    change Dop E (pinv (Dop E) (x - y)) ∈ LinearMap.ker (LinearMap.adjoint (delta0 (gameGraph E)))
    rw [map_pinv_of_mem _ _ hxyR, LinearMap.mem_ker]
    exact adjoint_sub_pinv _ x
  · rw [hN]
    show Dop E (u - pinv (Dop E) x) = 0
    rw [map_sub, hx, map_pinv, sub_self]

end Games

end Pbccb4299


open HarmonicGames.Decomposition Pbccb4299 Finset
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section
namespace HarmonicKernel
variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
  [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]

abbrev Opp (m : ι) := ∀ k : {k : ι // k ≠ m}, E k

def rest (m : ι) (p : ∀ k, E k) : Opp E m := fun k => p k

def rep (m : ι) (q : Opp E m) : ∀ k, E k :=
  fun k => if h : k = m then h.symm ▸ Classical.choice (inferInstance : Nonempty (E m)) else q ⟨k, h⟩

lemma rest_rep (m : ι) (q : Opp E m) : rest E m (rep E m q) = q := by
  funext k
  simp [rest, rep, k.2]

lemma nu_value (m : ι) (q : Opp E m) (p : ∀ k, E k) :
    nu E m q p = if rest E m p = q then 1 else 0 := by
  have he : (∀ k (hk : k ≠ m), p k = q ⟨k, hk⟩) ↔ rest E m p = q := by
    constructor
    · intro h
      funext k
      exact h k k.2
    · intro h k hk
      exact congrFun h ⟨k, hk⟩
  change (if ∀ k (hk : k ≠ m), p k = q ⟨k, hk⟩ then (1 : ℝ) else 0) = _
  simp only [he]

lemma mem_kernel (m : ι) (f : Util E) :
    f ∈ LinearMap.ker (Dm E m) ↔
      ∀ p q, rest E m p = rest E m q → f p = f q := by
  constructor
  · intro hf p q he
    by_cases hpq : p = q
    · rw [hpq]
    have hc : MComparable E m p q := ⟨hpq, fun k hk => congrFun he ⟨k, hk⟩⟩
    have hv := congrArg (fun x : Flow E => x p q) (LinearMap.mem_ker.mp hf)
    rw [Dm_apply, if_pos hc, one_mul] at hv
    change f q - f p = 0 at hv
    exact (sub_eq_zero.mp hv).symm
  · intro h
    apply LinearMap.mem_ker.mpr
    ext p q
    rw [Dm_apply]
    by_cases hc : MComparable E m p q
    · rw [if_pos hc, one_mul, h p q (by funext k; exact hc.2 k k.2), sub_self]
      rfl
    · rw [if_neg hc, zero_mul]
      rfl

lemma nu_kernel (m : ι) (q : Opp E m) : nu E m q ∈ LinearMap.ker (Dm E m) := by
  apply (mem_kernel E m _).mpr
  intro p r he
  rw [nu_value, nu_value, he]

lemma independent (m : ι) : LinearIndependent ℝ (nu E m) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc q
  have he := congrArg (fun f : Util E => f (rep E m q)) hc
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, nu_value, rest_rep,
    mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true, PiLp.zero_apply] at he
  exact he

lemma representation (m : ι) (f : Util E) (hf : f ∈ LinearMap.ker (Dm E m)) :
    f = ∑ q : Opp E m, f (rep E m q) • nu E m q := by
  classical
  ext p
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, nu_value,
    mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]
  exact (mem_kernel E m f).mp hf p _ (rest_rep E m _).symm

lemma span_kernel (m : ι) :
    Submodule.span ℝ (Set.range (nu E m)) = LinearMap.ker (Dm E m) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨q, rfl⟩
    exact nu_kernel E m q
  · intro f hf
    rw [representation E m f hf]
    exact Submodule.sum_mem _ (fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩))

lemma kernel_Pim (m : ι) : LinearMap.ker (Dm E m) = LinearMap.ker (Pim E m) := by
  ext f
  change Dm E m f = 0 ↔ pinv (Dm E m) (Dm E m f) = 0
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    have hh := congrArg (Dm E m) h
    rwa [map_pinv, map_zero] at hh

end HarmonicKernel


open HarmonicGames.Decomposition Pbccb4299 HarmonicKernel Finset
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section
namespace HarmonicDimensions
variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
  [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]

lemma kernel_components (u : Games E) :
    u ∈ LinearMap.ker (Dop E) ↔ ∀ m, u m ∈ LinearMap.ker (Dm E m) := by
  constructor
  · intro hu m
    apply LinearMap.mem_ker.mpr
    ext p q
    by_cases h : MComparable E m p q
    · rw [← Dop_single E m u p q h, LinearMap.mem_ker.mp hu]
    · rw [Dm_apply, if_neg h, zero_mul]; rfl
  · intro h
    apply LinearMap.mem_ker.mpr
    change ∑ m, Dm E m (u m) = 0
    exact sum_eq_zero (fun m _ => LinearMap.mem_ker.mp (h m))

def kernelEquiv : nonstrategicSubspace E ≃ₗ[ℝ] (∀ m, LinearMap.ker (Dm E m)) where
  toFun u m := ⟨u.1 m, (kernel_components E u.1).mp u.2 m⟩
  invFun v := ⟨WithLp.toLp 2 (fun m => (v m).1), (kernel_components E _).mpr (fun m => (v m).2)⟩
  left_inv u := Subtype.ext (PiLp.ext (fun _ => rfl))
  right_inv v := by funext m; rfl
  map_add' u v := by funext m; rfl
  map_smul' c u := by funext m; rfl

lemma card_opp (m : ι) : Fintype.card (Opp E m) =
    ∏ k ∈ univ.erase m, Fintype.card (E k) := by
  rw [Fintype.card_pi]
  exact (prod_subtype (univ.erase m) (by simp) (fun k => Fintype.card (E k))).symm

lemma dim_N : Module.finrank ℝ (nonstrategicSubspace E) =
    ∑ m, ∏ k ∈ univ.erase m, Fintype.card (E k) := by
  rw [(kernelEquiv E).finrank_eq, Module.finrank_pi_fintype]
  apply sum_congr rfl
  intro m _
  rw [← span_kernel E m, finrank_span_eq_card (independent E m), card_opp]

lemma dim_util : Module.finrank ℝ (Util E) = ∏ m, Fintype.card (E m) := by
  rw [(WithLp.linearEquiv 2 ℝ ((∀ m, E m) → ℝ)).finrank_eq, Module.finrank_pi, Fintype.card_pi]

lemma dim_games : Module.finrank ℝ (Games E) = Fintype.card ι * ∏ m, Fintype.card (E m) := by
  rw [(WithLp.linearEquiv 2 ℝ (∀ _ : ι, Util E)).finrank_eq, Module.finrank_pi_fintype]
  simp only [dim_util, sum_const, card_univ, smul_eq_mul]

lemma gradient_kernel_constant (f : Util E) (hf : f ∈ LinearMap.ker (delta0 (gameGraph E))) :
    ∀ p q, f p = f q := by
  have hm : ∀ m, f ∈ LinearMap.ker (Dm E m) := by
    intro m
    apply (mem_kernel E m f).mpr
    intro p q he
    by_cases hpq : p = q
    · rw [hpq]
    have ha : (gameGraph E).Adj p q := ⟨m, hpq, fun k hk => congrFun he ⟨k, hk⟩⟩
    have hh := congrArg (fun X : Flow E => X p q) (LinearMap.mem_ker.mp hf)
    change (if (gameGraph E).Adj p q then (1 : ℝ) else 0) * (f q - f p) = 0 at hh
    rw [if_pos ha, one_mul, sub_eq_zero] at hh
    exact hh.symm
  intro p q
  let v (s : Finset ι) : ∀ k, E k := fun k => if k ∈ s then q k else p k
  have hs : ∀ s, f (v s) = f p := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [v]
    | @insert m s hm' ih =>
      rw [(mem_kernel E m f).mp (hm m) (v (insert m s)) (v s) (by
        funext k
        simp [rest, v, k.2]), ih]
  have he : f q = f p := by simpa [v] using hs univ
  exact he.symm

lemma dim_gradient_kernel : Module.finrank ℝ (LinearMap.ker (delta0 (gameGraph E))) = 1 := by
  let onev : Util E := WithLp.toLp 2 (fun _ => (1 : ℝ))
  let p : ∀ m, E m := fun m => Classical.choice (inferInstance : Nonempty (E m))
  have hne : onev ≠ 0 := by
    intro h
    have hh := congrArg (fun f : Util E => f p) h
    norm_num [onev] at hh
  have he : LinearMap.ker (delta0 (gameGraph E)) = Submodule.span ℝ {onev} := by
    apply le_antisymm
    · intro f hf
      apply Submodule.mem_span_singleton.mpr
      refine ⟨f p, ?_⟩
      ext q
      change f p * 1 = f q
      rw [mul_one]
      exact gradient_kernel_constant E f hf p q
    · apply Submodule.span_le.mpr
      intro f hf
      have hf' : f = onev := Set.mem_singleton_iff.mp hf
      rw [hf']
      apply LinearMap.mem_ker.mpr
      ext a b
      change (if (gameGraph E).Adj a b then (1 : ℝ) else 0) * (1 - 1) = 0
      ring
  rw [he, finrank_span_singleton hne]

lemma dim_gradient_range : Module.finrank ℝ (LinearMap.range (delta0 (gameGraph E))) + 1 =
    ∏ m, Fintype.card (E m) := by
  have h := (delta0 (gameGraph E)).finrank_range_add_finrank_ker
  simpa only [dim_gradient_kernel, dim_util] using h

def potentialMap : potentialSubspace E →ₗ[ℝ] LinearMap.range (delta0 (gameGraph E)) where
  toFun u := ⟨Dop E u.1, u.2.2⟩
  map_add' u v := Subtype.ext (map_add (Dop E) u.1 v.1)
  map_smul' c u := Subtype.ext (map_smul (Dop E) c u.1)

lemma potential_bijective : Function.Bijective (potentialMap E) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    apply Subtype.ext
    apply eq_zero_of_fix_ker E
    · exact ((LinearMap.mem_eqLocus).mp u.2.1).symm
    · exact congrArg Subtype.val hu
  · intro v
    have hvD : v.1 ∈ LinearMap.range (Dop E) := by
      obtain ⟨f, hf⟩ := v.2
      rw [← hf]
      exact delta0_mem_range E f
    have he : Dop E (pinv (Dop E) v.1) = v.1 := map_pinv_of_mem _ _ hvD
    refine ⟨⟨pinv (Dop E) v.1, ?_⟩, ?_⟩
    · refine ⟨(LinearMap.mem_eqLocus).mpr (PiOp_fix E _ (pinv_mem _ _)).symm, ?_⟩
      change Dop E (pinv (Dop E) v.1) ∈ LinearMap.range (delta0 (gameGraph E))
      rw [he]
      exact v.2
    · exact Subtype.ext he

lemma dim_P : Module.finrank ℝ (potentialSubspace E) + 1 = ∏ m, Fintype.card (E m) := by
  rw [(LinearEquiv.ofBijective (potentialMap E) (potential_bijective E)).finrank_eq]
  exact dim_gradient_range E

lemma dim_sum : Module.finrank ℝ (potentialSubspace E) +
    Module.finrank ℝ (harmonicSubspace E) + Module.finrank ℝ (nonstrategicSubspace E) =
      Fintype.card ι * ∏ m, Fintype.card (E m) := by
  let P := potentialSubspace E
  let H := harmonicSubspace E
  let N := nonstrategicSubspace E
  have hPH : P ⊓ H = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    change v = 0
    have hh := uniq E v (-v) 0 hv.1 (H.neg_mem hv.2) N.zero_mem (by abel)
    exact hh.1
  have hPHN : (P ⊔ H) ⊓ N = ⊥ := by
    apply le_antisymm _ bot_le
    intro v hv
    change v = 0
    obtain ⟨p, hp, h, hh, he⟩ := Submodule.mem_sup.mp hv.1
    have hz := uniq E p h (-v) hp hh (N.neg_mem hv.2) (by rw [he]; abel)
    rw [hz.1, hz.2.1, zero_add] at he
    exact he.symm
  have htop : (P ⊔ H) ⊔ N = ⊤ := by
    apply eq_top_iff.mpr
    intro u _
    obtain ⟨hs, hp, hh, hn⟩ := part2 E u
    apply Submodule.mem_sup.mpr
    refine ⟨potentialComponent E u + harmonicComponent E u, ?_, nonstrategicComponent E u, hn, hs⟩
    exact Submodule.mem_sup.mpr ⟨_, hp, _, hh, rfl⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq P H
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (P ⊔ H) N
  rw [hPH, finrank_bot, add_zero] at h1
  rw [htop, hPHN, finrank_top, finrank_bot, add_zero, dim_games] at h2
  change Module.finrank ℝ P + Module.finrank ℝ H + Module.finrank ℝ N = _
  omega

end HarmonicDimensions

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] :
    (Module.finrank ℝ (HarmonicGames.GenericPure.potentialSubspace E) : ℤ) =
        (∏ m, (Fintype.card (E m) : ℤ)) - 1 ∧
      (Module.finrank ℝ (HarmonicGames.GenericPure.harmonicSubspace E) : ℤ) =
        ((Fintype.card ι : ℤ) - 1) * (∏ m, (Fintype.card (E m) : ℤ)) -
          (∑ m, ∏ k ∈ univ.erase m, (Fintype.card (E k) : ℤ)) + 1 ∧
      (Module.finrank ℝ (nonstrategicSubspace E) : ℤ) =
        ∑ m, ∏ k ∈ univ.erase m, (Fintype.card (E k) : ℤ) := by
  have hN : (Module.finrank ℝ (nonstrategicSubspace E) : ℤ) =
      ∑ m, ∏ k ∈ univ.erase m, (Fintype.card (E k) : ℤ) := by
    exact_mod_cast HarmonicDimensions.dim_N E
  have hP : (Module.finrank ℝ (potentialSubspace E) : ℤ) + 1 =
      ∏ m, (Fintype.card (E m) : ℤ) := by
    exact_mod_cast HarmonicDimensions.dim_P E
  have hS : (Module.finrank ℝ (potentialSubspace E) : ℤ) +
      (Module.finrank ℝ (harmonicSubspace E) : ℤ) + (Module.finrank ℝ (nonstrategicSubspace E) : ℤ) =
      (Fintype.card ι : ℤ) * ∏ m, (Fintype.card (E m) : ℤ) := by
    exact_mod_cast HarmonicDimensions.dim_sum E
  change (Module.finrank ℝ (potentialSubspace E) : ℤ) = _ ∧
    (Module.finrank ℝ (harmonicSubspace E) : ℤ) = _ ∧ _
  refine ⟨by linarith, ?_, hN⟩
  nlinarith

#print axioms solution
