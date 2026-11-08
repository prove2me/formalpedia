-- Prove2me | solution 1 for HarmonicGames.Decomposition.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T06:40:52.286913+00:00
-- url     : https://prove2.me/submissions/e6112250-932c-416d-9c11-4c1c615f851b

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Pinv
import Definitions.Def_HarmonicGames_Decomposition_Flows
import Definitions.Def_HarmonicGames_Decomposition_Games
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

theorem solution (ι : Type) [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] (m : ι) :
    LinearMap.ker (Dm E m) = LinearMap.ker (Pim E m) ∧
    LinearMap.ker (Pim E m) = LinearMap.ker (Delta0m E m) ∧
    LinearIndependent ℝ (nu E m) ∧
    Submodule.span ℝ (Set.range (nu E m)) = LinearMap.ker (Dm E m) := by
  refine ⟨HarmonicKernel.kernel_Pim E m, ?_, HarmonicKernel.independent E m, HarmonicKernel.span_kernel E m⟩
  rw [← HarmonicKernel.kernel_Pim, Delta0m, LinearMap.ker_adjoint_comp_self]

#print axioms solution
