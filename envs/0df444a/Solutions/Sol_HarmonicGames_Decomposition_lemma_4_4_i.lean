-- Prove2me | solution 1 for HarmonicGames.Decomposition.lemma_4_4_i
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T06:46:15.792947+00:00
-- url     : https://prove2.me/submissions/8a1b2a79-0f5f-4a00-ac5c-7c913e9ea703

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


open HarmonicGames.Decomposition Pbccb4299 HarmonicKernel Finset
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace HarmonicNormalized
variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
  [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]

lemma inner_nu (m : ι) (p : ∀ k, E k) (f : Util E) :
    inner ℝ (nu E m (rest E m p)) f = ∑ a : E m, f (Function.update p m a) := by
  classical
  have hset : univ.image (fun a => Function.update p m a) =
      univ.filter (fun q => rest E m q = rest E m p) := by
    ext q
    simp only [mem_image, mem_univ, true_and, mem_filter]
    constructor
    · rintro ⟨a, rfl⟩
      funext k
      exact Function.update_of_ne k.2 a p
    · intro he
      refine ⟨q m, ?_⟩
      funext k
      by_cases hk : k = m
      · subst k; simp
      · rw [Function.update_of_ne hk]
        exact (congrFun he ⟨k, hk⟩).symm
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, nu_value, ite_mul, one_mul, zero_mul]
  rw [← sum_filter, ← hset, sum_image]
  intro a _ b _ hab
  exact Function.update_injective p m hab

lemma orth_iff (m : ι) (f : Util E) : f ∈ (LinearMap.ker (Dm E m))ᗮ ↔
    ∀ p, ∑ a : E m, f (Function.update p m a) = 0 := by
  classical
  constructor
  · intro hf p
    rw [← inner_nu E m p f]
    exact Submodule.inner_right_of_mem_orthogonal (nu_kernel E m _) hf
  · intro h
    apply (Submodule.mem_orthogonal _ _).mpr
    intro w hw
    rw [representation E m w hw, sum_inner]
    apply sum_eq_zero
    intro q _
    rw [real_inner_smul_left]
    have hh := h (rep E m q)
    rw [← inner_nu E m (rep E m q) f, rest_rep] at hh
    rw [hh, mul_zero]

lemma Pim_fix_iff (m : ι) (f : Util E) :
    Pim E m f = f ↔ f ∈ (LinearMap.ker (Dm E m))ᗮ := by
  change pinv (Dm E m) (Dm E m f) = f ↔ _
  rw [pinv_apply_self, Submodule.starProjection_eq_self_iff]

end HarmonicNormalized


open HarmonicGames.Decomposition Pbccb4299 HarmonicKernel HarmonicNormalized Finset
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace HarmonicDm
variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type)
  [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)]

lemma inner_Dm (m : ι) (f : Util E) (X : Flow E) :
    inner ℝ (Dm E m f) X = -∑ a, f a * ∑ b, Wm E m a b * X a b := by
  have h0 : inner ℝ (Dm E m f) X = innerC1 (gameGraph E) (Dm E m f) X := rfl
  have hterm : ∀ a b, (if (gameGraph E).Adj a b then Dm E m f a b * X a b else 0) =
      (f b - f a) * (Wm E m a b * X a b) := by
    intro a b
    by_cases h : (gameGraph E).Adj a b
    · rw [if_pos h, Dm_apply, Wm]; ring
    · rw [if_neg h, Wm, if_neg (fun hc => h ⟨m, hc⟩), zero_mul, mul_zero]
  have hanti : ∀ a b, Wm E m b a * X b a = -(Wm E m a b * X a b) := by
    intro a b
    have hs : MComparable E m b a ↔ MComparable E m a b := (mGraph E m).adj_comm b a
    by_cases h : MComparable E m a b
    · simp only [Wm, if_pos h, if_pos (hs.mpr h), one_mul]
      exact C1.antisymm (gameGraph E) X ⟨m, h⟩
    · simp only [Wm, if_neg h, if_neg (fun hb => h (hs.mp hb)), zero_mul, neg_zero]
  rw [h0, innerC1]
  simp_rw [hterm, sub_mul, sum_sub_distrib]
  have h1 : ∑ a, ∑ b, f b * (Wm E m a b * X a b) =
      -∑ a, ∑ b, f a * (Wm E m a b * X a b) := by
    rw [sum_comm, ← sum_neg_distrib]
    apply sum_congr rfl
    intro a _
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro b _
    rw [hanti a b]; ring
  rw [h1]
  simp_rw [mul_sum]
  ring

lemma adjoint_value (m : ι) (X : Flow E) (p : ∀ k, E k) :
    (LinearMap.adjoint (Dm E m) X) p = -∑ q, Wm E m p q * X p q := by
  let g : Util E := WithLp.toLp 2 (fun p => -∑ q, Wm E m p q * X p q)
  have he : LinearMap.adjoint (Dm E m) X = g := by
    apply ext_inner_left ℝ
    intro f
    rw [LinearMap.adjoint_inner_right, inner_Dm, PiLp.inner_apply]
    simp only [Real.inner_apply]
    change -(∑ a, f a * ∑ b, Wm E m a b * X a b) =
      ∑ a, f a * (-∑ b, Wm E m a b * X a b)
    simp only [mul_neg, sum_neg_distrib]
  exact congrArg (fun f : Util E => f p) he

/- The change of summation is adapted from Nickrobbins95, accepted submission
   f84cddad-8723-492d-b9a4-8265f4f48a33, lemma sum_mcomp. -/
lemma sum_mcomp (m : ι) (f : (∀ k, E k) → ℝ) (a : ∀ k, E k) :
    ∑ b, (if MComparable E m a b then (1:ℝ) else 0) * (f b - f a) =
      ∑ c : E m, (f (Function.update a m c) - f a) := by
  have himg : ∑ c : E m, (f (Function.update a m c) - f a) =
      ∑ b ∈ univ.image (fun c => Function.update a m c), (f b - f a) := by
    rw [sum_image]
    intro x _ y _ hxy
    exact Function.update_injective a m hxy
  rw [himg, ← sum_subset (subset_univ (univ.image fun c => Function.update a m c))]
  · apply sum_congr rfl
    intro b hb
    obtain ⟨c, _, rfl⟩ := mem_image.mp hb
    split_ifs with hc
    · ring
    · have he : Function.update a m c = a := by
        by_contra hne
        exact hc ⟨fun e => hne e.symm, fun k hk => (Function.update_of_ne hk c a).symm⟩
      rw [he]; ring
  · intro b _ hb
    split_ifs with hc
    · exfalso
      apply hb
      refine mem_image.mpr ⟨b m, mem_univ _, ?_⟩
      funext k
      by_cases hk : k = m
      · subst k; simp
      · rw [Function.update_of_ne hk]; exact hc.2 k hk
    · ring

lemma laplacian_value (m : ι) (f : Util E) (p : ∀ k, E k) :
    Delta0m E m f p = (Fintype.card (E m) : ℝ) * f p -
      ∑ a : E m, f (Function.update p m a) := by
  change (LinearMap.adjoint (Dm E m) (Dm E m f)) p = _
  rw [adjoint_value]
  have he : ∀ q, Wm E m p q * Dm E m f p q =
      (if MComparable E m p q then (1 : ℝ) else 0) * (f q - f p) := by
    intro q
    rw [Wm, Dm_apply]
    split_ifs <;> ring
  simp_rw [he]
  rw [sum_mcomp, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  ring

end HarmonicDm

theorem solution (ι : Type) [Fintype ι] [DecidableEq ι] (E : ι → Type)
    [∀ m, Fintype (E m)] [∀ m, DecidableEq (E m)] [∀ m, Nonempty (E m)] (m : ι) :
    pinv (Dm E m) = (1 / (Fintype.card (E m) : ℝ)) • LinearMap.adjoint (Dm E m) := by
  have hn : (Fintype.card (E m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply LinearMap.ext
  intro X
  have hnrm := (HarmonicNormalized.orth_iff E m (pinv (Dm E m) X)).mp (pinv_mem _ _)
  have hadj : LinearMap.adjoint (Dm E m) (Dm E m (pinv (Dm E m) X)) =
      LinearMap.adjoint (Dm E m) X := by
    apply ext_inner_left ℝ
    intro f
    rw [LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
    have hh := inner_map_sub_pinv (Dm E m) X f
    rw [inner_sub_right, sub_eq_zero] at hh
    exact hh.symm
  ext p
  have he := HarmonicDm.laplacian_value E m (pinv (Dm E m) X) p
  change (LinearMap.adjoint (Dm E m) (Dm E m (pinv (Dm E m) X))) p = _ at he
  rw [hadj, hnrm p, sub_zero] at he
  change (pinv (Dm E m) X) p = (1 / (Fintype.card (E m) : ℝ)) * (LinearMap.adjoint (Dm E m) X) p
  rw [he]
  field_simp

#print axioms solution
