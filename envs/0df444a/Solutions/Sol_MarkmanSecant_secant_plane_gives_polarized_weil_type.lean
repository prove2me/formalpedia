-- Prove2me | solution 1 for MarkmanSecant.secant_plane_gives_polarized_weil_type
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T05:08:29.092333+00:00
-- url     : https://prove2.me/submissions/62bc95f3-793d-427d-adc0-8d785ae54e8a

import Mathlib
import Definitions.Def_MarkmanSecant
import Theorems.Thm_MarkmanSecant_expS_isEvenPureSpinor_annih
import Theorems.Thm_MarkmanSecant_exp_secant_plane_in_hodge_ring
import Theorems.Thm_MarkmanSecant_similarity_commutes_with_complex_structure
import Theorems.Thm_MarkmanSecant_exists_rational_similarity_of_secant

/-!
Complete proof of the polarized Weil-type structure from the exponential secant.

The contraction matrix is rational and nondegenerate. Its graph annihilators
are complementary. Rational similarity and commutation use already proved
platform lemmas. Projection to the dual coordinates identifies the relevant
Hodge eigenspaces with those of a real complex structure, of dimension n.
The polarization form is the negative sum of two ample positive forms.

Attribution: the imported exponential-spinor and Hodge-plane results are due
to Nickrobbins95. The imported commutation result is due to fizzyinc3. The
MKAux naturality/invariance helpers below reproduce the latter's accepted
submission 11519d8d-6234-4150-905e-cf073f5f6def. The degree-two contraction
argument is also used in Nickrobbins95's submission
383570f0-6dc2-4b73-8abc-4cf26ee6b4fd.
-/

set_option backward.isDefEq.respectTransparency false



set_option backward.isDefEq.respectTransparency false

open MarkmanSecant
open scoped ExteriorAlgebra

noncomputable section

namespace MarkmanRationalCoordinates

def spinBasis (n : ℕ) : Module.Basis (Finset (Fin (2 * n))) ℂ (Spinor n) :=
  (Pi.basisFun ℂ (Fin (2 * n))).ExteriorAlgebra

def ratSpan (n : ℕ) : Submodule ℚ (Spinor n) :=
  Submodule.span ℚ (Set.range (spinBasis n))

lemma basis_mem (n : ℕ) (s : Finset (Fin (2 * n))) : spinBasis n s ∈ ratSpan n :=
  Submodule.subset_span (Set.mem_range_self s)

lemma basis_empty (n : ℕ) : spinBasis n ∅ = 1 := by
  simp [spinBasis, ExteriorAlgebra.basis_apply, ExteriorAlgebra.ιMulti_family]

lemma basis_singleton (n : ℕ) (i : Fin (2 * n)) :
    spinBasis n {i} = ExteriorAlgebra.ι ℂ (Pi.single i 1) := by
  rw [spinBasis, ExteriorAlgebra.basis_apply_ofCard _ (Finset.card_singleton i)]
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply,
    Set.powersetCard.ofCard, Set.powersetCard.ofFinEmbEquiv, Finset.orderEmbOfFin_singleton]

lemma basis_mul_mem (n : ℕ) (s t : Finset (Fin (2 * n))) :
    spinBasis n s * spinBasis n t ∈ ratSpan n := by
  classical
  let s' : Set.powersetCard (Fin (2 * n)) s.card := ⟨s, rfl⟩
  let t' : Set.powersetCard (Fin (2 * n)) t.card := ⟨t, rfl⟩
  by_cases h : Disjoint s t
  · have he := ExteriorAlgebra.basis_mul_of_disjoint
      (Pi.basisFun ℂ (Fin (2 * n))) s' t' h
    change _ ∈ ratSpan n
    rw [show spinBasis n s * spinBasis n t = _ from he]
    exact (ratSpan n).toAddSubgroup.zsmul_mem (basis_mem n _) _
  · have he := ExteriorAlgebra.basis_mul_of_not_disjoint
      (Pi.basisFun ℂ (Fin (2 * n))) s' t' h
    rw [show spinBasis n s * spinBasis n t = 0 from he]
    exact (ratSpan n).zero_mem

lemma mul_mem (n : ℕ) (x y : Spinor n) (hx : x ∈ ratSpan n) (hy : y ∈ ratSpan n) :
    x * y ∈ ratSpan n := by
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨t, rfl⟩ := hy; exact basis_mul_mem n s t
    | zero => simpa using (ratSpan n).zero_mem
    | add y z _ _ hy hz => simpa [mul_add] using (ratSpan n).add_mem hy hz
    | smul c y _ hy => simpa [mul_smul_comm] using (ratSpan n).smul_mem c hy
  | zero => simpa using (ratSpan n).zero_mem
  | add x z _ _ hx hz => simpa [add_mul] using (ratSpan n).add_mem (hx y hy) (hz y hy)
  | smul c x _ hx => simpa [smul_mul_assoc] using (ratSpan n).smul_mem c (hx y hy)

lemma monomial_mem (n : ℕ) (l : List (Fin (2 * n))) : monomial l ∈ ratSpan n := by
  induction l with
  | nil => simpa [monomial, basis_empty] using basis_mem n ∅
  | cons i l ih =>
    simpa [monomial] using mul_mem n (ExteriorAlgebra.ι ℂ (Pi.single i 1)) (monomial l)
      (by rw [← basis_singleton]; exact basis_mem n {i}) ih

lemma integral_mem (n : ℕ) (s : Spinor n) (hs : IsIntegralClass s) : s ∈ ratSpan n := by
  induction hs using Submodule.span_induction with
  | mem x hx => obtain ⟨l, rfl⟩ := hx; exact monomial_mem n l
  | zero => exact (ratSpan n).zero_mem
  | add x y _ _ hx hy => exact (ratSpan n).add_mem hx hy
  | smul c x _ hx => exact (ratSpan n).toAddSubgroup.zsmul_mem hx c

lemma rational_mem (n : ℕ) (s : Spinor n) (hs : IsRationalClass s) : s ∈ ratSpan n := by
  obtain ⟨m, hm, hs⟩ := hs
  have h := (ratSpan n).smul_mem ((m : ℚ)⁻¹) (integral_mem n _ hs)
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hcast : ((m : ℚ)⁻¹) • ((m : ℂ) • s) = ((m : ℂ)⁻¹) • ((m : ℂ) • s) := by
    simpa using ratCast_smul_eq ℚ ℂ ((m : ℚ)⁻¹) ((m : ℂ) • s)
  rw [hcast, smul_smul, inv_mul_cancel₀ hm0, one_smul] at h
  exact h

lemma basis_is_monomial (n : ℕ) (s : Finset (Fin (2 * n))) :
    ∃ l : List (Fin (2 * n)), spinBasis n s = monomial l := by
  rw [spinBasis, ExteriorAlgebra.basis_apply]
  refine ⟨List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.prodEquiv.symm s).2), ?_⟩
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
    monomial, List.map_ofFn, Function.comp_def, Pi.basisFun_apply]

lemma dual_single (n : ℕ) (i j : Fin (2 * n)) :
    dualOf (Pi.single i 1) (Pi.single j 1) = if i = j then (1 : ℂ) else 0 := by
  classical
  simp [dualOf, dualLin, LinearMap.sum_apply, LinearMap.smulRight_apply,
    Pi.single_apply]

lemma contract_monomial_mem (n : ℕ) (j : Fin (2 * n)) (l : List (Fin (2 * n))) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n)))
      (dualOf (Pi.single j 1)) (monomial l) ∈ ratSpan n := by
  classical
  induction l with
  | nil => simp [monomial]
  | cons i l ih =>
    change CliffordAlgebra.contractLeft (dualOf (Pi.single j 1))
      (ExteriorAlgebra.ι ℂ (Pi.single i 1) * monomial l) ∈ ratSpan n
    rw [CliffordAlgebra.contractLeft_ι_mul, dual_single]
    have hprod := mul_mem n (ExteriorAlgebra.ι ℂ (Pi.single i 1)) _
      (by rw [← basis_singleton]; exact basis_mem n {i}) ih
    apply (ratSpan n).sub_mem
    · split_ifs <;> simp [monomial_mem]
    · exact hprod

lemma contract_mem (n : ℕ) (j : Fin (2 * n)) (s : Spinor n) (hs : s ∈ ratSpan n) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n)))
      (dualOf (Pi.single j 1)) s ∈ ratSpan n := by
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨l, hl⟩ := basis_is_monomial n s
    rw [hl]
    exact contract_monomial_mem n j l
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using (ratSpan n).add_mem hx hy
  | smul c x _ hx =>
    simpa only [LinearMap.map_smul_of_tower] using (ratSpan n).smul_mem c hx

lemma cliff_single_mem (n : ℕ) (s : Spinor n) (hs : s ∈ ratSpan n) (j : VIdx n) :
    cliffAt s (Pi.single j 1) ∈ ratSpan n := by
  classical
  change ExteriorAlgebra.ι ℂ (wPart (Pi.single j 1)) * s +
    CliffordAlgebra.contractLeft (dualOf (tPart (Pi.single j 1))) s ∈ ratSpan n
  cases j with
  | inl j =>
    have hw : wPart (Pi.single (Sum.inl j) (1 : ℂ)) = Pi.single j 1 := by
      ext i
      simp [wPart, Pi.single_apply]
    have ht : tPart (Pi.single (Sum.inl j) (1 : ℂ)) = 0 := by
      ext i
      simp [tPart, Pi.single_apply]
    rw [hw, ht]
    simp only [dualOf, map_zero, LinearMap.zero_apply, add_zero]
    exact mul_mem n _ s (by rw [← basis_singleton]; exact basis_mem n {j}) hs
  | inr j =>
    have hw : wPart (Pi.single (Sum.inr j) (1 : ℂ)) = 0 := by
      ext i
      simp [wPart, Pi.single_apply]
    have ht : tPart (Pi.single (Sum.inr j) (1 : ℂ)) = Pi.single j 1 := by
      ext i
      simp [tPart, Pi.single_apply]
    rw [hw, ht, map_zero, zero_mul, zero_add]
    exact contract_mem n j s hs

def cliffMatrix (n : ℕ) (s : Spinor n) :
    Matrix (Finset (Fin (2 * n))) (VIdx n) ℂ :=
  LinearMap.toMatrix' ((spinBasis n).equivFun.toLinearMap ∘ₗ cliffAt s)

lemma rational_cliffMatrix (n : ℕ) (s : Spinor n) (hs : IsRationalClass s) :
    ∃ M : Matrix (Finset (Fin (2 * n))) (VIdx n) ℚ,
      M.map (algebraMap ℚ ℂ) = cliffMatrix n s := by
  classical
  have hc (i : Finset (Fin (2 * n))) (j : VIdx n) :
      ∃ q : ℚ, (q : ℂ) = cliffMatrix n s i j := by
    have hm := cliff_single_mem n s (rational_mem n s hs) j
    have hh := ((spinBasis n).mem_span_iff_repr_mem ℚ _).mp hm i
    simpa [cliffMatrix, LinearMap.toMatrix'_apply, Module.Basis.equivFun_apply] using hh
  choose M hM using hc
  refine ⟨M, ?_⟩
  ext i j
  exact hM i j


end MarkmanRationalCoordinates


set_option backward.isDefEq.respectTransparency false

open MarkmanSecant MarkmanRationalCoordinates Matrix
open scoped ExteriorAlgebra

noncomputable section

namespace MarkmanThetaGeometry

def thetaL {n : ℕ} (Θ : Spinor n) : H1 n →ₗ[ℂ] H1 n :=
  ExteriorAlgebra.ιInv ∘ₗ
    (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n)))).flip Θ ∘ₗ dualLin

lemma thetaL_apply {n : ℕ} (Θ : Spinor n) (y : H1 n) : thetaL Θ y = theta Θ y := rfl

/-- The degree-two contraction argument also appears in Nickrobbins95's accepted
proof of expS_isEvenPureSpinor_annih (submission 383570f0-6dc2-4b73-8abc-4cf26ee6b4fd). -/
lemma iota_theta {n : ℕ} (Θ : Spinor n) (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n)) (y : H1 n) :
    ExteriorAlgebra.ι ℂ (theta Θ y) = CliffordAlgebra.contractLeft (dualOf y) Θ := by
  have hmem : Θ ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : H1 n →ₗ[ℂ] Spinor n) *
      LinearMap.range (ExteriorAlgebra.ι ℂ : H1 n →ₗ[ℂ] Spinor n) := by
    have h : Θ ∈ LinearMap.range (ExteriorAlgebra.ι ℂ : H1 n →ₗ[ℂ] Spinor n) ^ 2 := hΘ
    rwa [pow_two] at h
  have hcontract : CliffordAlgebra.contractLeft (dualOf y) Θ ∈
      LinearMap.range (ExteriorAlgebra.ι ℂ : H1 n →ₗ[ℂ] Spinor n) := by
    refine Submodule.mul_induction_on hmem ?_ ?_
    · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      rw [CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι,
        ← Algebra.commutes, ← Algebra.smul_def]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _))
        (Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _))
    · intro x z hx hz
      simpa only [map_add] using Submodule.add_mem _ hx hz
  obtain ⟨u, hu⟩ := hcontract
  unfold theta
  rw [← hu, ExteriorAlgebra.ι_leftInverse]

lemma basis_coordinate_iota {n : ℕ} (y : H1 n) (i : Fin (2 * n)) :
    (spinBasis n).equivFun (ExteriorAlgebra.ι ℂ y) {i} = y i := by
  classical
  have hy : ExteriorAlgebra.ι ℂ y =
      ∑ j : Fin (2 * n), y j • spinBasis n {j} := by
    have h := congrArg (ExteriorAlgebra.ι ℂ) ((Pi.basisFun ℂ (Fin (2 * n))).sum_repr y)
    simpa [map_sum, map_smul, basis_singleton] using h.symm
  rw [hy]
  simp [map_sum, map_smul, Finsupp.single_apply]

lemma rational_theta_matrix {n : ℕ} (Θ : Spinor n)
    (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n)) (hint : IsIntegralClass Θ) :
    ∃ T : Matrix (Fin (2 * n)) (Fin (2 * n)) ℚ,
      T.map (algebraMap ℚ ℂ) = LinearMap.toMatrix' (thetaL Θ) := by
  classical
  have h (i j : Fin (2 * n)) : ∃ q : ℚ, (q : ℂ) = theta Θ (Pi.single j 1) i := by
    have hm := contract_mem n j Θ (integral_mem n Θ hint)
    rw [← iota_theta Θ hΘ] at hm
    have hh := ((spinBasis n).mem_span_iff_repr_mem ℚ _).mp hm {i}
    simpa [← Module.Basis.equivFun_apply, basis_coordinate_iota] using hh
  choose T hT using h
  refine ⟨T, ?_⟩
  ext i j
  exact hT i j

lemma formEval_eq_dot {n : ℕ} (Θ : Spinor n) (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n))
    (a b : H1 n) : formEval Θ a b = b ⬝ᵥ theta Θ a := by
  unfold formEval
  rw [← iota_theta Θ hΘ, CliffordAlgebra.contractLeft_ι]
  simp [dualOf, dualLin, LinearMap.sum_apply, LinearMap.smulRight_apply, dotProduct]

lemma theta_injective_of_ample {n : ℕ}
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (Θ : Spinor n)
    (hΘ : IsAmpleClass J Θ) : Function.Injective (theta Θ) := by
  obtain ⟨T, hT⟩ := rational_theta_matrix Θ hΘ.1 hΘ.2.1
  let S : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ := T.map (algebraMap ℚ ℝ)
  have ht (y : H1 n) : theta Θ y = (T.map (algebraMap ℚ ℂ)).mulVec y := by
    rw [hT, LinearMap.toMatrix'_mulVec]
    rfl
  have hreal (x : Fin (2 * n) → ℝ) : theta Θ (realH1 x) = realH1 (S.mulVec x) := by
    ext i
    simp [ht, realH1, S, Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
  have hzR (x : Fin (2 * n) → ℝ) (hx : S.mulVec x = 0) : x = 0 := by
    by_contra hx0
    have hp := hΘ.2.2.2 x hx0
    have hz : theta Θ (realH1 x) = 0 := by rw [hreal, hx]; rfl
    rw [formEval_eq_dot Θ hΘ.1, hz, dotProduct_zero] at hp
    exact (lt_irrefl 0) hp
  have hzC (y : H1 n) (hy : theta Θ y = 0) : y = 0 := by
    have hr : S.mulVec (fun i => (y i).re) = 0 := by
      ext i
      have hh := congrArg Complex.re (congrFun hy i)
      simpa [ht, S, Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re] using hh
    have hi : S.mulVec (fun i => (y i).im) = 0 := by
      ext i
      have hh := congrArg Complex.im (congrFun hy i)
      simpa [ht, S, Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im] using hh
    have hre := hzR _ hr
    have him := hzR _ hi
    ext i
    exact Complex.ext (congrFun hre i) (congrFun him i)
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzC
  change thetaL Θ (x - y) = 0
  rw [map_sub, thetaL_apply, thetaL_apply, hxy, sub_self]

lemma theta_re {n : ℕ} (Θ : Spinor n) (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n))
    (hint : IsIntegralClass Θ) (y : H1 n) :
    theta Θ (realH1 (fun i => (y i).re)) = realH1 (fun i => (theta Θ y i).re) := by
  obtain ⟨T, hT⟩ := rational_theta_matrix Θ hΘ hint
  have ht (y : H1 n) : theta Θ y = (T.map (algebraMap ℚ ℂ)).mulVec y := by
    rw [hT, LinearMap.toMatrix'_mulVec]
    rfl
  ext i
  simp [ht, realH1, Matrix.mulVec, dotProduct, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_sum, Complex.ofReal_mul]

lemma theta_real_surjective {n : ℕ}
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (Θ : Spinor n)
    (hΘ : IsAmpleClass J Θ) (x : Fin (2 * n) → ℝ) :
    ∃ y : Fin (2 * n) → ℝ, theta Θ (realH1 y) = realH1 x := by
  have hinj : Function.Injective (thetaL Θ) := theta_injective_of_ample J Θ hΘ
  obtain ⟨y, hy⟩ := LinearMap.surjective_of_injective hinj (realH1 x)
  refine ⟨fun i => (y i).re, ?_⟩
  rw [theta_re Θ hΘ.1 hΘ.2.1]
  change theta Θ y = realH1 x at hy
  rw [hy]
  simp [realH1]


end MarkmanThetaGeometry


set_option backward.isDefEq.respectTransparency false

open MarkmanSecant MarkmanThetaGeometry Matrix
open scoped ExteriorAlgebra

noncomputable section

namespace MarkmanExpGeometry

lemma exp_annih_disjoint {n : ℕ}
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (Θ : Spinor n)
    (hΘ : IsAmpleClass J Θ) (c : ℂ) (hc : c ≠ 0) :
    annih (expS (c • Θ)) ⊓ annih (expS ((-c) • Θ)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  change v = 0
  have hp := (expS_isEvenPureSpinor_annih n Θ hΘ.1 c).2 v |>.mp hv.1
  have hm := (expS_isEvenPureSpinor_annih n Θ hΘ.1 (-c)).2 v |>.mp hv.2
  simp only [neg_smul, neg_neg] at hm
  have he : c • theta Θ (tPart v) = -(c • theta Θ (tPart v)) := hm.symm.trans hp
  have hz : (2 : ℂ) • (c • theta Θ (tPart v)) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr he
  have ht : theta Θ (tPart v) = 0 :=
    (smul_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))).resolve_left hc
  have hvT : tPart v = 0 := theta_injective_of_ample J Θ hΘ (by
    simpa only [← thetaL_apply, map_zero] using ht)
  have hvW : wPart v = 0 := by simpa [ht] using hp
  ext i
  cases i with
  | inl i => exact congrFun hvW i
  | inr i => exact congrFun hvT i

lemma annih_sup_top {n : ℕ} (Θ : Spinor n) (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n)) (c : ℂ)
    (hdis : annih (expS (c • Θ)) ⊓ annih (expS ((-c) • Θ)) = ⊥) :
    annih (expS (c • Θ)) ⊔ annih (expS ((-c) • Θ)) = ⊤ := by
  have hp := (expS_isEvenPureSpinor_annih n Θ hΘ c).1
  have hm := (expS_isEvenPureSpinor_annih n Θ hΘ (-c)).1
  apply Submodule.eq_top_of_finrank_eq
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (annih (expS (c • Θ))) (annih (expS ((-c) • Θ)))
  rw [hdis, finrank_bot, hp.2.2, hm.2.2] at h
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  omega

lemma opposite_action_blocks {n : ℕ} (Θ : Spinor n)
    (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n)) (c d : ℂ) (hcc : c * c = -d)
    (hdis : annih (expS (c • Θ)) ⊓ annih (expS ((-c) • Θ)) = ⊥)
    (f : VC n →ₗ[ℂ] VC n)
    (hp : ∀ v ∈ annih (expS (c • Θ)), f v = c • v)
    (hm : ∀ v ∈ annih (expS ((-c) • Θ)), f v = (-c) • v)
    (v : VC n) :
    wPart (f v) = d • theta Θ (tPart v) ∧ theta Θ (tPart (f v)) = -wPart v := by
  have hv : v ∈ annih (expS (c • Θ)) ⊔ annih (expS ((-c) • Θ)) := by
    rw [annih_sup_top Θ hΘ c hdis]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  have hxw := (expS_isEvenPureSpinor_annih n Θ hΘ c).2 x |>.mp hx
  have hyw := (expS_isEvenPureSpinor_annih n Θ hΘ (-c)).2 y |>.mp hy
  change wPartLin x = -(c • thetaL Θ (tPartLin x)) at hxw
  change wPartLin y = -((-c) • thetaL Θ (tPartLin y)) at hyw
  simp only [neg_smul, neg_neg] at hyw
  change wPartLin (f (x + y)) = d • thetaL Θ (tPartLin (x + y)) ∧
    thetaL Θ (tPartLin (f (x + y))) = -wPartLin (x + y)
  constructor
  · simp only [map_add, map_neg, hp x hx, hm y hy, map_smul, hxw, hyw,
      smul_neg, smul_smul, neg_mul, hcc, neg_smul, neg_neg, smul_add]
  · simp only [map_add, map_neg, hp x hx, hm y hy, map_smul, hxw, hyw, neg_smul]
    abel


end MarkmanExpGeometry


set_option backward.isDefEq.respectTransparency false

open MarkmanSecant MarkmanThetaGeometry MarkmanExpGeometry Matrix
open scoped ExteriorAlgebra

noncomputable section

namespace MarkmanPolarization

/-- Block-coordinate identities used also by fizzyinc3 in accepted submission
11519d8d-6234-4150-905e-cf073f5f6def. -/
lemma wPart_IV {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (v : VC n) :
    wPart (IV J *ᵥ v) = cMat J *ᵥ wPart v := by
  ext i
  simp [wPart, IV, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]

lemma tPart_IV {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (v : VC n) :
    tPart (IV J *ᵥ v) = -((cMat J).transpose *ᵥ tPart v) := by
  ext i
  simp [tPart, IV, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]

lemma positive_form_nonneg {n : ℕ}
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (Θ : Spinor n)
    (hΘ : IsAmpleClass J Θ) (x : Fin (2 * n) → ℝ) :
    0 ≤ (formEval Θ (realH1 x) ((-(cMat J).transpose).mulVec (realH1 x))).re := by
  by_cases hx : x = 0
  · subst x
    rw [formEval_eq_dot Θ hΘ.1]
    have hz : realH1 (0 : Fin (2 * n) → ℝ) = 0 := rfl
    rw [hz, Matrix.mulVec_zero, zero_dotProduct]
    simp
  · exact (hΘ.2.2.2 x hx).le

lemma negative_of_action {n : ℕ}
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (Θ : Spinor n)
    (hΘ : IsAmpleClass J Θ) (d : ℚ) (hd : 0 < d) (c : ℂ)
    (hcc : c * c = -(d : ℂ))
    (hdis : annih (expS (c • Θ)) ⊓ annih (expS ((-c) • Θ)) = ⊥)
    (f : VC n →ₗ[ℂ] VC n)
    (hp : ∀ v ∈ annih (expS (c • Θ)), f v = c • v)
    (hm : ∀ v ∈ annih (expS ((-c) • Θ)), f v = (-c) • v)
    (hcomm : ∀ v, f ((IV J).mulVec v) = (IV J).mulVec (f v))
    (x : VIdx n → ℝ) (hx : x ≠ 0) :
    (pairV (f ((IV J).mulVec (realV x))) (realV x)).re < 0 := by
  let w : Fin (2 * n) → ℝ := fun i => x (Sum.inl i)
  let t : Fin (2 * n) → ℝ := fun i => x (Sum.inr i)
  obtain ⟨b, hb⟩ := theta_real_surjective J Θ hΘ w
  have hw : wPart (realV x) = realH1 w := rfl
  have ht : tPart (realV x) = realH1 t := rfl
  have hblocks := opposite_action_blocks Θ hΘ.1 c (d : ℂ) hcc hdis f hp hm (realV x)
  have hfw : wPart (f (realV x)) = (d : ℂ) • theta Θ (realH1 t) := by
    simpa only [ht] using hblocks.1
  have hft : tPart (f (realV x)) = -realH1 b := by
    apply theta_injective_of_ample J Θ hΘ
    rw [hblocks.2, hw]
    change -realH1 w = thetaL Θ (-realH1 b)
    rw [map_neg, thetaL_apply, hb]
  have hpair : pairV (f ((IV J).mulVec (realV x))) (realV x) =
      -formEval Θ (realH1 b) ((-(cMat J).transpose).mulVec (realH1 b)) -
        (d : ℂ) * formEval Θ (realH1 t) ((-(cMat J).transpose).mulVec (realH1 t)) := by
    rw [hcomm, pairV, tPart_IV, wPart_IV, hft, hfw, hw, ht, ← hb,
      formEval_eq_dot Θ hΘ.1, formEval_eq_dot Θ hΘ.1]
    simp only [Matrix.mulVec_neg, neg_neg, Matrix.mulVec_smul, dotProduct_smul,
      smul_eq_mul, Matrix.neg_mulVec, neg_dotProduct, mul_neg, sub_neg_eq_add]
    congr 1
    congr 1
    rw [← Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  rw [hpair, Complex.sub_re, Complex.neg_re, Complex.mul_re]
  simp only [Complex.ratCast_re, Complex.ratCast_im, zero_mul, sub_zero]
  have hb0 := positive_form_nonneg J Θ hΘ b
  have ht0 := positive_form_nonneg J Θ hΘ t
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  by_cases hbne : b = 0
  · have htne : t ≠ 0 := by
      intro htzero
      apply hx
      have hwzero : realH1 w = 0 := by
        rw [← hb, hbne]
        change thetaL Θ 0 = 0
        exact map_zero _
      ext i
      cases i with
      | inl i =>
        have h := congrArg Complex.re (congrFun hwzero i)
        simpa [realH1, w] using h
      | inr i => exact congrFun htzero i
    have htp := hΘ.2.2.2 t htne
    nlinarith
  · have hbp := hΘ.2.2.2 b hbne
    have hdt : 0 ≤ (d : ℝ) *
        (formEval Θ (realH1 t) ((-(cMat J).transpose).mulVec (realH1 t))).re :=
      mul_nonneg hdR.le ht0
    linarith


end MarkmanPolarization


set_option backward.isDefEq.respectTransparency false

open MarkmanSecant Matrix

noncomputable section

namespace MarkmanComplexDimension

def imagEigenspace {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) :
    Submodule ℂ (H1 n) := LinearMap.ker ((cMat J).mulVecLin - Complex.I • LinearMap.id)

lemma mem_imagEigenspace {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (v : H1 n) : v ∈ imagEigenspace J ↔ (cMat J).mulVec v = Complex.I • v := by
  change (cMat J).mulVec v - Complex.I • v = 0 ↔ _
  exact sub_eq_zero

lemma finrank_imagEigenspace (n : ℕ)
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1) :
    Module.finrank ℂ (imagEigenspace J) = n := by
  let R : imagEigenspace J →ₗ[ℝ] (Fin (2 * n) → ℝ) :=
    { toFun := fun v i => (v.val i).re
      map_add' := by intro u v; ext i; simp
      map_smul' := by intro r v; ext i; simp }
  have hrel (v : imagEigenspace J) :
      (fun i => (v.val i).im) = -J.mulVec (fun i => (v.val i).re) := by
    have hv := (mem_imagEigenspace J v.val).mp v.property
    ext i
    have hh := congrArg Complex.re (congrFun hv i)
    simp [cMat, Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re] at hh
    change (v.val i).im = -(J.mulVec (fun i => (v.val i).re) i)
    change J.mulVec (fun i => (v.val i).re) i = -(v.val i).im at hh
    linarith
  have hinj : Function.Injective R := by
    intro u v h
    apply Subtype.ext
    funext i
    apply Complex.ext (congrFun h i)
    have hi : (fun i => (u.val i).im) = (fun i => (v.val i).im) := by
      rw [hrel u, hrel v]
      exact congrArg (fun x => -J.mulVec x) h
    exact congrFun hi i
  have hcast (y : Fin (2 * n) → ℝ) :
      (cMat J).mulVec (realH1 y) = realH1 (J.mulVec y) := by
    ext i
    simp [cMat, realH1, Matrix.mulVec, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
  have hsurj : Function.Surjective R := by
    intro x
    let z : H1 n := realH1 x - Complex.I • realH1 (J.mulVec x)
    have hsq : J.mulVec (J.mulVec x) = -x := by
      rw [Matrix.mulVec_mulVec, hJ, Matrix.neg_mulVec, Matrix.one_mulVec]
    have hneg : realH1 (-x) = -realH1 x := by ext i; simp [realH1]
    have hz : z ∈ imagEigenspace J := by
      rw [mem_imagEigenspace]
      dsimp only [z]
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hcast, hcast, hsq, hneg]
      simp only [smul_sub, smul_neg, smul_smul, Complex.I_mul_I,
        neg_one_smul, sub_neg_eq_add]
      abel
    refine ⟨⟨z, hz⟩, ?_⟩
    ext i
    simp [R, z, realH1, Complex.mul_re]
  have hr := (LinearEquiv.ofBijective R ⟨hinj, hsurj⟩).finrank_eq
  have ht := Module.finrank_mul_finrank ℝ ℂ (imagEigenspace J)
  rw [Complex.finrank_real_complex] at ht
  rw [Module.finrank_fin_fun] at hr
  omega


end MarkmanComplexDimension

namespace MKAux
variable {n : ℕ}

lemma dual_apply (t w : H1 n) : dualLin t w = ∑ i, t i * w i := by
  simp [dualLin, LinearMap.sum_apply, LinearMap.smulRight_apply]

lemma contract_map (f : H1 n →ₗ[ℂ] H1 n) (d : Module.Dual ℂ (H1 n)) (x : Spinor n) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n))) d (ExteriorAlgebra.map f x) =
    ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n))) (d ∘ₗ f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x m hx =>
    rw [map_mul]
    have h1 : ExteriorAlgebra.map f (CliffordAlgebra.ι (0 : QuadraticForm ℂ (H1 n)) m) =
        CliffordAlgebra.ι (0 : QuadraticForm ℂ (H1 n)) (f m) := ExteriorAlgebra.map_apply_ι f m
    rw [h1, CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι_mul, hx, map_sub,
      map_smul, map_mul, h1]
    rfl

lemma cliffAt_apply (s : Spinor n) (v : VC n) :
    cliffAt s v = ExteriorAlgebra.ι ℂ (wPart v) * s +
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (H1 n))) (dualLin (tPart v)) s := by
  rfl

/-- The complex structure `J` acting on `H¹`. -/
noncomputable def Jl (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : H1 n →ₗ[ℂ] H1 n :=
  Matrix.mulVecLin (cMat J)

lemma scal_I (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : scal J Complex.I = Jl J := by
  simp [scal, Jl]

lemma cMat_sq (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1) :
    cMat J * cMat J = -1 := by
  ext i j
  have h := congrArg (fun M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ => ((M i j : ℝ) : ℂ)) hJ
  simp only [Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul] at h
  simp only [cMat, Matrix.mul_apply, Matrix.map_apply, h]
  by_cases hij : i = j <;> simp [hij, Matrix.one_apply]

lemma hodge_fixed (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (s : Spinor n) (hs : IsInHodgeRing J s) :
    ExteriorAlgebra.map (Jl J) s = s := by
  obtain ⟨c, hc, rfl⟩ := hs
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p _
  have h := (hc p).2 Complex.I
  rw [scal_I] at h
  rw [h]
  have : Complex.I ^ p * (starRingEnd ℂ) Complex.I ^ p = 1 := by
    rw [← mul_pow, Complex.conj_I]; simp
  rw [this, one_smul]

lemma wPart_IV (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (v : VC n) :
    wPart (IV J *ᵥ v) = cMat J *ᵥ wPart v := by
  ext i
  simp [wPart, IV, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]

lemma tPart_IV (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (v : VC n) :
    tPart (IV J *ᵥ v) = -((cMat J).transpose *ᵥ tPart v) := by
  ext i
  simp [tPart, IV, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks]

lemma annih_inv (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1) (s : Spinor n)
    (hs : ExteriorAlgebra.map (Jl J) s = s) (v : VC n) (hv : v ∈ annih s) :
    IV J *ᵥ v ∈ annih s := by
  have hv' : cliffAt s v = 0 := hv
  show cliffAt s (IV J *ᵥ v) = 0
  have h0 := congrArg (ExteriorAlgebra.map (Jl J)) hv'
  rw [map_zero, cliffAt_apply, map_add, map_mul, ExteriorAlgebra.map_apply_ι, hs] at h0
  -- the contraction term
  set G : H1 n →ₗ[ℂ] H1 n := -(Jl J) with hG
  have hGJ : G ∘ₗ Jl J = LinearMap.id := by
    apply LinearMap.ext; intro y
    simp only [hG, LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply, Jl,
      Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, cMat_sq J hJ]
    rw [Matrix.neg_mulVec, Matrix.one_mulVec, neg_neg]
  have hc := contract_map (Jl J) (dualLin (tPart v) ∘ₗ G) s
  rw [hs, LinearMap.comp_assoc, hGJ, LinearMap.comp_id] at hc
  rw [← hc] at h0
  rw [cliffAt_apply, wPart_IV, tPart_IV]
  have hd : dualLin (-((cMat J).transpose *ᵥ tPart v)) = dualLin (tPart v) ∘ₗ G := by
    apply LinearMap.ext; intro y
    rw [dual_apply, LinearMap.comp_apply, dual_apply]
    simp only [hG, LinearMap.neg_apply, Jl, Matrix.mulVecLin_apply]
    simp only [Pi.neg_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, neg_mul,
      Finset.sum_neg_distrib, mul_neg, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [hd]
  exact h0

end MKAux


set_option backward.isDefEq.respectTransparency false

open MarkmanSecant MarkmanThetaGeometry MarkmanComplexDimension Matrix
open scoped ExteriorAlgebra

noncomputable section

namespace MarkmanExpDimension

lemma mem_V10 {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (v : VC n) : v ∈ V10 J ↔ (IV J).mulVec v = Complex.I • v := by
  change (IV J).mulVec v - Complex.I • v = 0 ↔ _
  exact sub_eq_zero

lemma exp_dimension (n : ℕ)
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1)
    (Θ : Spinor n) (hΘ : Θ ∈ ⋀[ℂ]^2 (H1 n))
    (hhodge : HasHodgeType J 1 1 Θ) (c : ℂ) :
    Module.finrank ℂ ↥(annih (expS (c • Θ)) ⊓ V10 J) = n := by
  let K : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ := -J.transpose
  have hK : K * K = -1 := by
    dsimp only [K]
    rw [neg_mul_neg, ← Matrix.transpose_mul, hJ]
    simp
  have hcK : cMat K = -(cMat J).transpose := by
    ext i j
    simp [cMat, K]
  have htheta : ExteriorAlgebra.map (MKAux.Jl J) Θ = Θ := by
    have h := hhodge Complex.I
    rw [MKAux.scal_I] at h
    simpa using h
  have hfixed : ExteriorAlgebra.map (MKAux.Jl J) (expS (c • Θ)) = expS (c • Θ) := by
    simp only [expS, map_sum, map_smul, map_pow, htheta]
  let S := annih (expS (c • Θ)) ⊓ V10 J
  have hT (v : S) : tPart v.val ∈ imagEigenspace K := by
    rw [mem_imagEigenspace, hcK, Matrix.neg_mulVec]
    have h := congrArg tPartLin ((mem_V10 J v.val).mp v.property.2)
    change tPart ((IV J).mulVec v.val) = Complex.I • tPart v.val at h
    rwa [MKAux.tPart_IV] at h
  let R : S →ₗ[ℂ] imagEigenspace K :=
    { toFun := fun v => ⟨tPart v.val, hT v⟩
      map_add' := by intro u v; apply Subtype.ext; rfl
      map_smul' := by intro a v; apply Subtype.ext; rfl }
  have hinj : Function.Injective R := by
    intro u v h
    have ht : tPart u.val = tPart v.val := congrArg Subtype.val h
    have hu := (expS_isEvenPureSpinor_annih n Θ hΘ c).2 u.val |>.mp u.property.1
    have hv := (expS_isEvenPureSpinor_annih n Θ hΘ c).2 v.val |>.mp v.property.1
    have hw : wPart u.val = wPart v.val := by rw [hu, hv, ht]
    apply Subtype.ext
    funext i
    cases i with
    | inl i => exact congrFun hw i
    | inr i => exact congrFun ht i
  have hsurj : Function.Surjective R := by
    intro y
    let v : VC n := Sum.elim (-(c • theta Θ y.val)) y.val
    have hvw : wPart v = -(c • theta Θ y.val) := rfl
    have hvt : tPart v = y.val := rfl
    have hvW : v ∈ annih (expS (c • Θ)) := by
      rw [(expS_isEvenPureSpinor_annih n Θ hΘ c).2 v, hvw, hvt]
    have hvIW := MKAux.annih_inv J hJ (expS (c • Θ)) hfixed v hvW
    have hvtI : tPart ((IV J).mulVec v) = Complex.I • y.val := by
      rw [MKAux.tPart_IV, hvt]
      have h := (mem_imagEigenspace K y.val).mp y.property
      simpa only [hcK, Matrix.neg_mulVec] using h
    have hvwI : wPart ((IV J).mulVec v) = Complex.I • wPart v := by
      rw [(expS_isEvenPureSpinor_annih n Θ hΘ c).2 _ |>.mp hvIW, hvtI, hvw]
      change -(c • thetaL Θ (Complex.I • y.val)) = Complex.I • -(c • thetaL Θ y.val)
      rw [map_smul]
      simp [smul_neg, smul_smul, mul_comm]
    have hvV : v ∈ V10 J := by
      rw [mem_V10]
      funext i
      cases i with
      | inl i => exact congrFun hvwI i
      | inr i => exact congrFun hvtI i
    refine ⟨⟨v, hvW, hvV⟩, ?_⟩
    apply Subtype.ext
    exact hvt
  calc
    Module.finrank ℂ S = Module.finrank ℂ (imagEigenspace K) :=
      (LinearEquiv.ofBijective R ⟨hinj, hsurj⟩).finrank_eq
    _ = n := finrank_imagEigenspace n K hK


end MarkmanExpDimension


set_option backward.isDefEq.respectTransparency false

open MarkmanSecant

noncomputable section

namespace MarkmanRationalClosure

lemma integral_nsmul {n : ℕ} (x : Spinor n) (hx : IsIntegralClass x) (m : ℕ) :
    IsIntegralClass ((m : ℂ) • x) := by
  rw [Nat.cast_smul_eq_nsmul]
  exact (Submodule.span ℤ (Set.range (monomial (n := n)))).toAddSubgroup.nsmul_mem hx m

lemma rational_add {n : ℕ} (x y : Spinor n)
    (hx : IsRationalClass x) (hy : IsRationalClass y) : IsRationalClass (x + y) := by
  obtain ⟨m, hm, hx⟩ := hx
  obtain ⟨k, hk, hy⟩ := hy
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  have hxm := integral_nsmul _ hx k
  have hym := integral_nsmul _ hy m
  have hsum := (Submodule.span ℤ (Set.range (monomial (n := n)))).add_mem hxm hym
  simpa only [IsIntegralClass, Nat.cast_mul, smul_add, smul_smul, mul_comm] using hsum

lemma rational_zero (n : ℕ) : IsRationalClass (0 : Spinor n) := by
  refine ⟨1, by omega, ?_⟩
  simp only [smul_zero]
  exact Submodule.zero_mem _

lemma rational_sum {n : ℕ} {I : Type*} (s : Finset I) (f : I → Spinor n)
    (hf : ∀ i ∈ s, IsRationalClass (f i)) : IsRationalClass (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rational_zero n
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact rational_add _ _ (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma rational_of_hodge {n : ℕ}
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (s : Spinor n)
    (hs : IsInHodgeRing J s) : IsRationalClass s := by
  obtain ⟨c, hc, rfl⟩ := hs
  exact rational_sum _ _ (fun p _ => (hc p).1)


end MarkmanRationalClosure


set_option backward.isDefEq.respectTransparency false

open MarkmanSecant MarkmanThetaGeometry MarkmanExpGeometry MarkmanPolarization
open MarkmanExpDimension MarkmanRationalClosure Matrix
open scoped ExteriorAlgebra

noncomputable section

private lemma root_sqrtNeg_sq (d : ℚ) (hd : 0 < d) : (sqrtNeg d) ^ 2 = -(d : ℂ) := by
  unfold sqrtNeg
  rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt (show 0 ≤ (d : ℝ) by exact_mod_cast hd.le)]
  push_cast
  ring

theorem solution (n : ℕ) (hn : 2 ≤ n)
    (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) (hJ : J * J = -1)
    (Θ : Spinor n) (hΘ : IsAmpleClass J Θ) (d : ℕ) (hd : 0 < d) :
    IsEvenPureSpinor (expS (sqrtNeg d • Θ)) ∧ IsEvenPureSpinor (expS ((-sqrtNeg d) • Θ)) ∧
      annih (expS (sqrtNeg d • Θ)) ⊓ annih (expS ((-sqrtNeg d) • Θ)) = ⊥ ∧
      ∃ F : Matrix (VIdx n) (VIdx n) ℚ,
        (∀ v ∈ annih (expS (sqrtNeg d • Θ)), (ratMatV F).mulVec v = sqrtNeg d • v) ∧
        (∀ v ∈ annih (expS ((-sqrtNeg d) • Θ)), (ratMatV F).mulVec v = (-sqrtNeg d) • v) ∧
        F * F = -((d : ℚ) • (1 : Matrix (VIdx n) (VIdx n) ℚ)) ∧
        (∀ x y : VIdx n → ℚ,
          pairV (ratV (F.mulVec x)) (ratV (F.mulVec y)) = (d : ℂ) * pairV (ratV x) (ratV y)) ∧
        ratMatV F * IV J = IV J * ratMatV F ∧
        Module.finrank ℂ ↥(annih (expS (sqrtNeg d • Θ)) ⊓ V10 J) = n ∧
        Module.finrank ℂ ↥(annih (expS ((-sqrtNeg d) • Θ)) ⊓ V10 J) = n ∧
        ∀ x : VIdx n → ℝ, x ≠ 0 →
          (pairV ((ratMatV F).mulVec ((IV J).mulVec (realV x))) (realV x)).re < 0 := by
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hcc : sqrtNeg (d : ℚ) * sqrtNeg (d : ℚ) = -(d : ℂ) := by
    simpa only [pow_two, Rat.cast_natCast] using root_sqrtNeg_sq (d : ℚ) hdQ
  have hc : sqrtNeg (d : ℚ) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcc
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
    exact hdC (neg_eq_zero.mp hcc.symm)
  have hp := (expS_isEvenPureSpinor_annih n Θ hΘ.1 (sqrtNeg d)).1
  have hm := (expS_isEvenPureSpinor_annih n Θ hΘ.1 (-sqrtNeg d)).1
  have hdis := exp_annih_disjoint J Θ hΘ (sqrtNeg d) hc
  obtain ⟨a, b, ha, hb, he1, he2⟩ := exp_secant_plane_in_hodge_ring n J hJ Θ hΘ d hd
  have h₁ : IsEvenPureSpinor (a + sqrtNeg d • b) := by rwa [← he1]
  have h₂ : IsEvenPureSpinor (a - sqrtNeg d • b) := by rwa [← he2]
  have h₁₂ : annih (a + sqrtNeg d • b) ⊓ annih (a - sqrtNeg d • b) = ⊥ := by
    rwa [← he1, ← he2]
  obtain ⟨F, hF₁, hF₂, hsq, hpair⟩ := exists_rational_similarity_of_secant
    n (d : ℚ) hdQ a b (rational_of_hodge J a ha) (rational_of_hodge J b hb) h₁ h₂ h₁₂
  have hFp : ∀ v ∈ annih (expS (sqrtNeg d • Θ)),
      (ratMatV F).mulVec v = sqrtNeg d • v := by simpa only [he1] using hF₁
  have hFm : ∀ v ∈ annih (expS ((-sqrtNeg d) • Θ)),
      (ratMatV F).mulVec v = (-sqrtNeg d) • v := by simpa only [he2] using hF₂
  have hcomm := similarity_commutes_with_complex_structure n J hJ (d : ℚ) hdQ
    a b ha hb h₁ h₂ h₁₂ F hF₁ hF₂
  refine ⟨hp, hm, hdis, F, hFp, hFm, hsq, ?_, hcomm, ?_, ?_, ?_⟩
  · simpa only [Rat.cast_natCast] using hpair
  · exact exp_dimension n J hJ Θ hΘ.1 hΘ.2.2.1 (sqrtNeg d)
  · exact exp_dimension n J hJ Θ hΘ.1 hΘ.2.2.1 (-sqrtNeg d)
  · intro x hx
    apply negative_of_action J Θ hΘ (d : ℚ) hdQ (sqrtNeg d)
      (by simpa only [Rat.cast_natCast] using hcc) hdis (ratMatV F).mulVecLin hFp hFm
    · intro v
      change (ratMatV F).mulVec ((IV J).mulVec v) = (IV J).mulVec ((ratMatV F).mulVec v)
      rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
    · exact hx



#print axioms solution
