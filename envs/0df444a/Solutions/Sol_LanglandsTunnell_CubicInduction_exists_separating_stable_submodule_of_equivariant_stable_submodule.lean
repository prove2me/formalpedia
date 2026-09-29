-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_separating_stable_submodule_of_equivariant_stable_submodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/564c5479-7373-5600-889d-815144332c89

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmoothSpace3
import Theorems.Thm_LanglandsTunnell_CubicInduction_archRealLift3_mul_eq_mul_archRealLift3_conj
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isotypicProjector_natural_of_orthFinite_of_derivStable
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finiteDimensional_forall_mem_hull_of_rotationType_of_smoothingSubmodule
import Theorems.Thm_LanglandsTunnell_CubicInduction_signProjection_read_kernel_stable_of_doubleSlotCoeffMap
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_stable_submodule_inf_eq_bot_and_sub_mem_of_positive_skew_form
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_separating_stable_submodule_of_equivariant_stable_submodule
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.CubicInduction

namespace CoreS

private noncomputable def _root_.CoreS.PIv (ε : Fin 3 → Fin 2) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (o : Fin 3 → Fin 3 → ℝ) : ℂ :=
  (1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
    F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) *
      (WhittakerBlock.archRealLift3 o * k₁))

p2m_export "CoreS" "PIv"

noncomputable def PIvLin (ε : Fin 3 → Fin 2) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) →ₗ[ℂ] ((Fin 3 → Fin 3 → ℝ) → ℂ) where
  toFun F o := PIv ε k₁ F o
  map_add' F G := by
    funext o
    simp only [PIv, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' z F := by
    funext o
    simp only [PIv, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring

theorem PIvLin_apply (ε : Fin 3 → Fin 2) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (o : Fin 3 → Fin 3 → ℝ) :
    PIvLin ε k₁ F o = PIv ε k₁ F o := rfl

theorem det_ne_zero_of_orth (o : Fin 3 → Fin 3 → ℝ) (ho : (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0)) : (Matrix.of o).det ≠ 0 := by
  have hT : (Matrix.of o).transpose * Matrix.of o = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply, ho i j]
  intro h
  have := congrArg Matrix.det hT
  rw [Matrix.det_mul, Matrix.det_transpose, h, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem lift_mul_comm_of_arch_one (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (m : Fin 3 → Fin 3 → ℝ) (hm : (Matrix.of m).det ≠ 0) :
    WhittakerBlock.archRealLift3 m * k₁ = k₁ * WhittakerBlock.archRealLift3 m := by
  obtain ⟨-, h⟩ := archRealLift3_mul_eq_mul_archRealLift3_conj k₁ m hm
  rw [h, hk₁, AutomorphicForm.StandardKernel.realMat_one, inv_one, one_mul, mul_one]
  rfl

theorem Phi_natural (M : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (h4 : ∀ w ∈ M, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) →
      archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 → (fun g => w (g * k)) ∈ M)
    (Λ : ↥M →ₗ[ℂ] (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (hΛb : ∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M) (k' : AdelicGL 3 (𝓞 ℚ) ℚ)
        (hk'₁ : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1)
        (hk'₂ : archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3),
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Λ ⟨fun x => v (x * k'), h4 v hv k' hk'₁ hk'₂⟩ g = Λ ⟨v, hv⟩ (g * k'))
    (ε : Fin 3 → Fin 2) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (X : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (hXM : X ≤ M)
    (hXK : ∀ w ∈ X, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) →
      archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 → (fun g => w (g * k)) ∈ X) :
    ∀ (u : ↥X) (r : Fin 3 → Fin 3 → ℝ) (hr : (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0))
        (k : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁' : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1)
        (hk₂ : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3),
        k = WhittakerBlock.archRealLift3 r →
        ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
          ((PIvLin ε k₁).comp (Λ.comp (Submodule.inclusion hXM)))
              ⟨fun g => (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g * k), hXK u u.2 k hk₁' hk₂⟩ o =
            ((PIvLin ε k₁).comp (Λ.comp (Submodule.inclusion hXM))) u (fun i j => ∑ k : Fin 3, o i k * r k j) := by
  intro u r hr k hk₁' hk₂ hk o ho
  simp only [LinearMap.comp_apply, PIvLin_apply, PIv]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  have hb := hΛb (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hXM u.2) k hk₁' hk₂
    (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) *
      (WhittakerBlock.archRealLift3 o * k₁))
  have hincl : (Submodule.inclusion hXM ⟨fun g => (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g * k), hXK u u.2 k hk₁' hk₂⟩ : ↥M) =
      ⟨fun x => (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x * k), h4 (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hXM u.2) k hk₁' hk₂⟩ := rfl
  have hincl' : (Submodule.inclusion hXM u : ↥M) = ⟨(u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), hXM u.2⟩ := rfl
  rw [hincl, hincl', hb]
  congr 1
  have ho' := det_ne_zero_of_orth o ho
  have hr' := det_ne_zero_of_orth r hr
  rw [hk, mul_assoc, mul_assoc, ← lift_mul_comm_of_arch_one k₁ hk₁ r hr', ← mul_assoc (WhittakerBlock.archRealLift3 o),
    WhittakerBlock.archRealLift3_mul ho' hr']
  congr 2

theorem orth_mul (o r : Fin 3 → Fin 3 → ℝ) (ho : (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0)) (hr : (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0)) :
    ∀ i j : Fin 3, ∑ a : Fin 3, (fun i j => ∑ k : Fin 3, o i k * r k j) a i * (fun i j => ∑ k : Fin 3, o i k * r k j) a j =
      if i = j then 1 else 0 := by
  have hO : (Matrix.of o).transpose * Matrix.of o = 1 := by
    ext i j; simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply, ho i j]
  have hR : (Matrix.of r).transpose * Matrix.of r = 1 := by
    ext i j; simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply, hr i j]
  have hP : (Matrix.of o * Matrix.of r).transpose * (Matrix.of o * Matrix.of r) = 1 := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.of o).transpose, hO, Matrix.one_mul, hR]
  intro i j
  have := congr_fun (congr_fun hP i) j
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply] using this

theorem det_cast_mul (o r : Fin 3 → Fin 3 → ℝ) :
    (Matrix.of fun i j : Fin 3 => (((fun i j => ∑ k : Fin 3, o i k * r k j) i j : ℝ) : ℂ)).det =
      (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det * (Matrix.of fun i j : Fin 3 => ((r i j : ℝ) : ℂ)).det := by
  rw [← Matrix.det_mul]
  congr 1
  ext i j
  simp [Matrix.mul_apply]

theorem eval_eq_sum_of_isHomogeneous_one (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous 1) :
    ∃ c : Fin 3 → ℂ, ∀ x : Fin 3 → ℂ, MvPolynomial.eval x p = ∑ i : Fin 3, c i * x i := by
  classical
  refine ⟨fun i => p.coeff (Finsupp.single i 1), fun x => ?_⟩
  have key : ∀ d ∈ p.support, ∃ i : Fin 3, d = Finsupp.single i 1 := by
    intro d hd
    have hdeg : (Finsupp.weight (1 : Fin 3 → ℕ)) d = 1 := hp (MvPolynomial.mem_support_iff.1 hd)
    have hcard : Multiset.card (Finsupp.toMultiset d) = 1 := by
      rw [Finsupp.card_toMultiset]
      simpa [Finsupp.weight, Finsupp.linearCombination, Finsupp.sum] using hdeg
    obtain ⟨i, hi⟩ := Multiset.card_eq_one.1 hcard
    refine ⟨i, ?_⟩
    rw [← Finsupp.toMultiset_toFinsupp d, hi, Multiset.toFinsupp_singleton]
  have hpeq : p = ∑ i : Fin 3, MvPolynomial.C (p.coeff (Finsupp.single i 1)) * MvPolynomial.X i := by
    ext d
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
    by_cases hd : d ∈ p.support
    · obtain ⟨i, rfl⟩ := key d hd
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
      · simp
      · intro j _ hj
        have : Finsupp.single j 1 ≠ Finsupp.single i 1 := fun h =>
          hj ((Finsupp.single_left_inj one_ne_zero).1 h)
        simp [this]
    · have h0 : p.coeff d = 0 := by simpa [MvPolynomial.mem_support_iff] using hd
      rw [h0]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs with h
      · subst h; simp [h0]
      · simp
  conv_lhs => rw [hpeq]
  simp [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

theorem eval_aeval_col0 (x : Fin 3 × Fin 3 → ℂ) (p : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) = MvPolynomial.eval (fun a : Fin 3 => x (a, 0)) p := by
  have h := congrArg (fun φ : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] ℂ => φ p)
    (MvPolynomial.comp_aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) (MvPolynomial.aeval x))
  simp only [AlgHom.comp_apply, MvPolynomial.coe_aeval_eq_eval, MvPolynomial.aeval_X] at h
  simpa [MvPolynomial.coe_aeval_eq_eval] using h

theorem read_tauType (M : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (Λ : ↥M →ₗ[ℂ] (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (ε : Fin 3 → Fin 2) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (X : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (hXM : X ≤ M)
    (ℓ : ℕ) (hℓ : ℓ = 0 ∨ ℓ = 1) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hvX : v ∈ X)
    (hvread : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      PIv ε k₁ (Λ ⟨v, hXM hvX⟩) o = (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p)) :
    (ℓ = 0 ∧ (∀ o r : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → (∀ i j : Fin 3, ∑ a : Fin 3, r a i * r a j = if i = j then 1 else 0) →
        ((PIvLin ε k₁).comp (Λ.comp (Submodule.inclusion hXM))) ⟨v, hvX⟩ (fun i j => ∑ k : Fin 3, o i k * r k j) =
          (Matrix.of fun i j : Fin 3 => ((r i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) * ((PIvLin ε k₁).comp (Λ.comp (Submodule.inclusion hXM))) ⟨v, hvX⟩ o)) ∨
    (ℓ = 1 ∧ (∃ c : Fin 3 → Fin 3 → ℂ, ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        ((PIvLin ε k₁).comp (Λ.comp (Submodule.inclusion hXM))) ⟨v, hvX⟩ o = (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          ∑ i : Fin 3, ∑ j : Fin 3, c i j * ((o i j : ℝ) : ℂ))) := by
  have hΦ : ∀ o, ((PIvLin ε k₁).comp (Λ.comp (Submodule.inclusion hXM))) ⟨v, hvX⟩ o = PIv ε k₁ (Λ ⟨v, hXM hvX⟩) o := fun o => rfl
  rcases hℓ with rfl | rfl
  · left
    refine ⟨rfl, fun o r ho hr => ?_⟩
    rw [hΦ, hΦ, hvread _ (orth_mul o r ho hr), hvread o ho, det_cast_mul, eval_aeval_col0, eval_aeval_col0]

    have hpC : p = MvPolynomial.C (p.coeff 0) := by
      by_cases h0 : p = 0
      · rw [h0]; simp
      · exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C).1 (hp.totalDegree h0)
    rw [hpC, MvPolynomial.eval_C, MvPolynomial.eval_C, mul_pow]
    ring
  · right
    obtain ⟨c, hc⟩ := eval_eq_sum_of_isHomogeneous_one p hp
    refine ⟨rfl, fun i j => if j = 0 then c i else 0, fun o ho => ?_⟩
    rw [hΦ, hvread o ho, eval_aeval_col0, hc]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single_of_mem (0 : Fin 3) (Finset.mem_univ _)]
    · simp
    · intro j _ hj; simp [hj]

end CoreS

noncomputable section

namespace CoreP47

abbrev G3 := AdelicGL 3 (𝓞 ℚ) ℚ
abbrev Fn := AdelicGL 3 (𝓞 ℚ) ℚ → ℂ

private def _root_.CoreP47.PIv (ε : Fin 3 → Fin 2) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (o : Fin 3 → Fin 3 → ℝ) : ℂ :=
  (1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
    F (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) *
      (WhittakerBlock.archRealLift3 o * k₁))

p2m_export "CoreP47" "PIv"
theorem PIv_add (ε : Fin 3 → Fin 2) (k₁ : G3) (F G : Fn) (o : Fin 3 → Fin 3 → ℝ) :
    PIv ε k₁ (F + G) o = PIv ε k₁ F o + PIv ε k₁ G o := by
  simp only [PIv, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem PIv_smul (ε : Fin 3 → Fin 2) (k₁ : G3) (c : ℂ) (F : Fn) (o : Fin 3 → Fin 3 → ℝ) :
    PIv ε k₁ (c • F) o = c * PIv ε k₁ F o := by
  simp only [PIv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun τ _ => by ring)

theorem PIv_zero (ε : Fin 3 → Fin 2) (k₁ : G3) (o : Fin 3 → Fin 3 → ℝ) : PIv ε k₁ 0 o = 0 := by
  simp only [PIv, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

def KSt (H : Submodule ℂ Fn) : Prop :=
  ∀ w ∈ H, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
      (fun g => w (g * k)) ∈ H

def DSt (H : Submodule ℂ Fn) : Prop := ∀ w ∈ H, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ H

def hullFam (M : Submodule ℂ Fn) (f : Fn) : Set (Submodule ℂ Fn) :=
  {H' | H' ≤ M ∧ f ∈ H' ∧ KSt H' ∧ DSt H'}

def hull (M : Submodule ℂ Fn) (f : Fn) : Submodule ℂ Fn := sInf (hullFam M f)

theorem mem_hull (M : Submodule ℂ Fn) (f : Fn) : f ∈ hull M f := by
  rw [hull, Submodule.mem_sInf]
  intro q hq
  exact hq.2.1

theorem hull_le_of_mem {M : Submodule ℂ Fn} {f : Fn} {X : Submodule ℂ Fn} (hX : X ∈ hullFam M f) :
    hull M f ≤ X :=
  sInf_le hX

theorem hull_KSt (M : Submodule ℂ Fn) (f : Fn) : KSt (hull M f) := by
  intro w hw k hk1 hk2
  rw [hull, Submodule.mem_sInf] at hw ⊢
  intro q hq
  exact hq.2.2.1 w (hw q hq) k hk1 hk2

theorem hull_DSt (M : Submodule ℂ Fn) (f : Fn) : DSt (hull M f) := by
  intro w hw i j
  rw [hull, Submodule.mem_sInf] at hw ⊢
  intro q hq
  exact hq.2.2.2 w (hw q hq) i j

theorem hull_min (M : Submodule ℂ Fn) (f : Fn) :
    ∀ H' : Submodule ℂ Fn, H' ≤ M → f ∈ H' → KSt H' → DSt H' → hull M f ≤ H' :=
  fun _ a b c d => sInf_le ⟨a, b, c, d⟩

def trSet (u : Fn) : Set Fn :=
  {w | ∃ k : AdelicGL 3 (𝓞 ℚ) ℚ,
    (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) ∧ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
      w = fun g => u (g * k)}

theorem span_trSet_le {H : Submodule ℂ Fn} (hK : KSt H) {u : Fn} (hu : u ∈ H) :
    Submodule.span ℂ (trSet u) ≤ H := by
  rw [Submodule.span_le]
  rintro w ⟨k, hk1, hk2, rfl⟩
  exact hK u hu k hk1 hk2

def restrictP {X H : Submodule ℂ Fn} (hHX : H ≤ X) (P₀ : ↥X →ₗ[ℂ] ↥X)
    (hP1 : ∀ u : ↥X, ((P₀ u : ↥X) : Fn) ∈ Submodule.span ℂ (trSet (u : Fn))) (hK : KSt H) :
    ↥H →ₗ[ℂ] ↥H where
  toFun u := ⟨((P₀ ⟨(u : Fn), hHX u.2⟩ : ↥X) : Fn), span_trSet_le hK u.2 (hP1 ⟨(u : Fn), hHX u.2⟩)⟩
  map_add' u w := by
    apply Subtype.ext
    have h : (⟨((u + w : ↥H) : Fn), hHX (u + w).2⟩ : ↥X) = ⟨(u : Fn), hHX u.2⟩ + ⟨(w : Fn), hHX w.2⟩ := rfl
    show ((P₀ ⟨((u + w : ↥H) : Fn), hHX (u + w).2⟩ : ↥X) : Fn) =
      ((P₀ ⟨(u : Fn), hHX u.2⟩ : ↥X) : Fn) + ((P₀ ⟨(w : Fn), hHX w.2⟩ : ↥X) : Fn)
    rw [h, map_add]
    rfl
  map_smul' c u := by
    apply Subtype.ext
    have h : (⟨((c • u : ↥H) : Fn), hHX (c • u).2⟩ : ↥X) = c • ⟨(u : Fn), hHX u.2⟩ := rfl
    show ((P₀ ⟨((c • u : ↥H) : Fn), hHX (c • u).2⟩ : ↥X) : Fn) = c • ((P₀ ⟨(u : Fn), hHX u.2⟩ : ↥X) : Fn)
    rw [h, map_smul]
    rfl

theorem restrictP_coe {X H : Submodule ℂ Fn} (hHX : H ≤ X) (P₀ : ↥X →ₗ[ℂ] ↥X)
    (hP1 : ∀ u : ↥X, ((P₀ u : ↥X) : Fn) ∈ Submodule.span ℂ (trSet (u : Fn))) (hK : KSt H) (u : ↥H) :
    ((restrictP hHX P₀ hP1 hK u : ↥H) : Fn) = ((P₀ ⟨(u : Fn), hHX u.2⟩ : ↥X) : Fn) := rfl

theorem finite_range_of_forall_mem {H : Submodule ℂ Fn} (P : ↥H →ₗ[ℂ] ↥H) (E : Submodule ℂ Fn)
    [FiniteDimensional ℂ ↥E] (hPE : ∀ u : ↥H, ((P u : ↥H) : Fn) ∈ E) :
    FiniteDimensional ℂ ↥(LinearMap.range P) := by
  let φ : ↥(LinearMap.range P) →ₗ[ℂ] ↥E :=
    { toFun := fun y => ⟨((y : ↥H) : Fn), by
        obtain ⟨x, hx⟩ := y.2
        rw [← hx]
        exact hPE x⟩
      map_add' := fun y y' => rfl
      map_smul' := fun c y => rfl }
  have hφ : Function.Injective φ := by
    intro y y' h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥E => (z : Fn)) h
  exact Module.Finite.of_injective φ hφ

def Orth (o : Fin 3 → Fin 3 → ℝ) : Prop := (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0)

set_option maxHeartbeats 1600000 in

theorem PROJDATA_of_P123
    (M : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (h1 :
      (∀ w ∈ M, WhittakerBlock.IsArchSmooth3 w ∧
        WhittakerBlock.IsArchSmooth3
          (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ w) ∧
        (∀ wd : List (Fin 3 × Fin 3),
          Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) w wd)) ∧
        ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), w (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = w g))
    (h3 :
      (∀ w ∈ M, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))))
    (h4 :
      (∀ w ∈ M, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M))
    (h5 : (∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M))
    (h10 :
      (∃ B : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ,
        (∀ w ∈ M, ∀ w' ∈ M, B w' w = (starRingEnd ℂ) (B w w')) ∧
        (∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ w' ∈ M, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') ∧
        (∀ w ∈ M, w ≠ 0 → 0 < (B w w).re) ∧
        (∀ w ∈ M, ∀ w' ∈ M, ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w')) ∧
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ M, ∀ w' ∈ M, B (fun g => w (g * k)) (fun g => w' (g * k)) = B w w'))
    (h11 :
      (∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ M,
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l] w)) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0))
    (h12 :
      (∀ v ∈ M, ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        v (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * v g))
    (h13 :
      (∀ v ∈ M, ∃ N : ℕ, ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) v w g‖ ≤ C * gauge3 ℚ g ^ N))
    (N₂ : ℕ) (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1)
    (N₃ : ℕ) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1)
    (hrel : ∀ w ∈ M,
      (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧ (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0)
    (ρ : ℝ) (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ) (hδ : 0 < δ) (he : Function.Injective e)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hexp : ∀ (N : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      WhittakerBlock.IsArchSmooth3 u →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] u) = 0) →
      (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] u) = 0) →
      (∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N) →
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ (ρ + δ)) ∧
        ∃ c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          (∀ i j i' j', Continuous (c' i j i' j')) ∧
          (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
            ‖c i j y₂ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₂ ^ (ρ + δ)) ∧
          (∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₂ : ℝ, 0 < y₂ → c i'' j'' y₂ k = 0) →
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i' : Fin n) (j' : Fin J), c' i j i' j' k = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₂ : ℝ), 0 < y₂ → c i j y₂ k = 0)) ∧
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₁ : ℝ, b⁻¹ ≤ y₁ → y₁ ≤ b → ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₁ k * ((y₂ : ℂ) ^ e i * ((Real.log y₂ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₂ ^ (ρ + δ)) ∧
        ∃ c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          (∀ i j i' j', Continuous (c' i j i' j')) ∧
          (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
            ‖c i j y₁ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₁ : ℂ) ^ e i' * ((Real.log y₁ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₁ ^ (ρ + δ)) ∧
          (∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₁ : ℝ, 0 < y₁ → c i'' j'' y₁ k = 0) →
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i' : Fin n) (j' : Fin J), c' i j i' j' k = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₁ : ℝ), 0 < y₁ → c i j y₁ k = 0)))
    (i9 i9' : Fin n) (j₀ j₀' : Fin J) (ν : Fin 3 → ℂ)
    (Λ : ↥M →ₗ[ℂ] (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (hΛa : (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M)
        (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
        ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => cv i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ v
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, cv i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous (cv' i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖cv i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, cv' i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ))) →
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, Λ ⟨v, hv⟩ k = cv' i9 j₀ i9' j₀' k))
    (hΛb : (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M) (k' : AdelicGL 3 (𝓞 ℚ) ℚ)
        (hk'₁ : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1)
        (hk'₂ : archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3),
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
          Λ ⟨fun x => v (x * k'), h4 v hv k' hk'₁ hk'₂⟩ g = Λ ⟨v, hv⟩ (g * k')))
    (hΛc : (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M) (c d : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => Λ ⟨v, hv⟩ (g * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0))
          (Λ ⟨WhittakerBlock.archDeriv c d v, h5 v hv c d⟩ g) 0))
    (ε : Fin 3 → Fin 2) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (ℓ : ℕ) (hℓ : ℓ = 0 ∨ ℓ = 1) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (X : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (hXM : X ≤ M) (hXK : ((∀ w ∈ X, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ X))) (hXD : ((∀ w ∈ X, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ X)))
    (hXeq : ∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u ∈ X), (∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Λ ⟨u, hXM hu⟩ (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * Λ ⟨u, hXM hu⟩ g))
    (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hvX : v ∈ X)
    (hvread : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨v, hXM hvX⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁))) =
        (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p))
    (B : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ) (hB : ((∀ w ∈ M, ∀ w' ∈ M, B w' w = (starRingEnd ℂ) (B w w')) ∧
        (∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ w' ∈ M, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') ∧
        (∀ w ∈ M, w ≠ 0 → 0 < (B w w).re) ∧
        (∀ w ∈ M, ∀ w' ∈ M, ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w')) ∧
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ M, ∀ w' ∈ M, B (fun g => w (g * k)) (fun g => w' (g * k)) = B w w'))
    (hP123 : ∃ P₀ : ↥X →ₗ[ℂ] ↥X,
      (∀ u : ↥X, ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈
        Submodule.span ℂ {w | ∃ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) ∧ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 ∧
            w = fun g => (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g * k)}) ∧
      (∀ u : ↥X, P₀ (P₀ u) = P₀ u) ∧
      (∀ u w : ↥X, B (P₀ u) w = B u (P₀ w)) ∧
      (∀ u : ↥X, ((ℓ = 0 ∧ ∀ i j : Fin 3, WhittakerBlock.archDeriv i j ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv j i ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = 0) ∨
           (ℓ = 1 ∧ (WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 0 1 ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 1 0 ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) - WhittakerBlock.archDeriv 1 0 (WhittakerBlock.archDeriv 0 1 ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 1 0 ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) +
            (WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 0 2 ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 2 0 ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) - WhittakerBlock.archDeriv 2 0 (WhittakerBlock.archDeriv 0 2 ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 2 0 ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) +
            (WhittakerBlock.archDeriv 1 2 (WhittakerBlock.archDeriv 1 2 ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 2 1 ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) - WhittakerBlock.archDeriv 2 1 (WhittakerBlock.archDeriv 1 2 ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - WhittakerBlock.archDeriv 2 1 ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) + (2 : ℂ) • ((P₀ u : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) = 0))) ∧
      ∃ f₀ : ↥X, P₀ f₀ = f₀ ∧
        ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
          PIv ε k₁ (Λ ⟨(f₀ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), hXM f₀.2⟩) o =
            (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
              MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p)) :
    ∃ (H : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (hHX : H ≤ X),
      (∀ w ∈ H, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ H) ∧ (∀ w ∈ H, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ H) ∧
      ∃ (N : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (hNH : N ≤ H),
        (∀ w ∈ N, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ N) ∧ (∀ w ∈ N, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ N) ∧
        (∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u ∈ H),
          (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) → PIv ε k₁ (Λ ⟨u, hXM (hHX hu)⟩) o = 0) → u ∈ N) ∧
        (∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u ∈ N), ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
          PIv ε k₁ (Λ ⟨u, hXM (hHX (hNH hu))⟩) o = 0) ∧
        ∃ (P : ↥H →ₗ[ℂ] ↥H),
          (∀ w : ↥H, (w : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ N → ((P w : ↥H) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) ∈ N) ∧
          (∀ w : ↥H, P (P w) = P w) ∧
          (∀ w w' : ↥H, B (P w) w' = B w (P w')) ∧
          FiniteDimensional ℂ ↥(LinearMap.range P) ∧
          ∃ (f : ↥H), P f = f ∧
            ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
              PIv ε k₁ (Λ ⟨(f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), hXM (hHX f.2)⟩) o =
                (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p)  := by
  classical
  obtain ⟨P₀, hP1, hP2, hP3, hP5, f₀, hf₀P, hf₀read⟩ := hP123

  have hXfam : X ∈ hullFam M (f₀ : Fn) := ⟨hXM, f₀.2, hXK, hXD⟩
  have hHX : hull M (f₀ : Fn) ≤ X := hull_le_of_mem hXfam
  have hHK : KSt (hull M (f₀ : Fn)) := hull_KSt M _
  have hHD : DSt (hull M (f₀ : Fn)) := hull_DSt M _
  have hfH : (f₀ : Fn) ∈ hull M (f₀ : Fn) := mem_hull M _
  have hHmin := hull_min M (f₀ : Fn)

  have hfτ := hP5 f₀
  rw [hf₀P] at hfτ

  obtain ⟨E, hEfin, hE⟩ :=
    LanglandsTunnell.CubicInduction.exists_finiteDimensional_forall_mem_hull_of_rotationType_of_smoothingSubmodule
      M ω h1 h3 h4 h5 h10 h11 h12 h13 N₂ a₂ ha₂ N₃ a₃ ha₃ hrel ρ n J e δ hδ he hre hexp 0 (Or.inl rfl) ℓ hℓ (f₀ : Fn) (hXM f₀.2) hfτ
      (hull M (f₀ : Fn)) (hHX.trans hXM) hfH hHK hHD hHmin

  let P : ↥(hull M (f₀ : Fn)) →ₗ[ℂ] ↥(hull M (f₀ : Fn)) := restrictP hHX P₀ hP1 hHK

  let N : Submodule ℂ Fn :=
    { carrier := {u | ∃ hu : u ∈ hull M (f₀ : Fn), ∀ o : Fin 3 → Fin 3 → ℝ, Orth o →
          PIv ε k₁ (Λ ⟨u, hXM (hHX hu)⟩) o = 0}
      zero_mem' := ⟨(hull M (f₀ : Fn)).zero_mem, fun o _ => by
          have h0 : (⟨(0 : Fn), hXM (hHX (hull M (f₀ : Fn)).zero_mem)⟩ : ↥M) = 0 := rfl
          rw [h0, map_zero, PIv_zero]⟩
      add_mem' := by
        rintro u w ⟨hu, hu0⟩ ⟨hw, hw0⟩
        refine ⟨(hull M (f₀ : Fn)).add_mem hu hw, fun o ho => ?_⟩
        have h : (⟨u + w, hXM (hHX ((hull M (f₀ : Fn)).add_mem hu hw))⟩ : ↥M) =
            ⟨u, hXM (hHX hu)⟩ + ⟨w, hXM (hHX hw)⟩ := rfl
        rw [h, map_add, PIv_add, hu0 o ho, hw0 o ho, add_zero]
      smul_mem' := by
        rintro c u ⟨hu, hu0⟩
        refine ⟨(hull M (f₀ : Fn)).smul_mem c hu, fun o ho => ?_⟩
        have h : (⟨c • u, hXM (hHX ((hull M (f₀ : Fn)).smul_mem c hu))⟩ : ↥M) = c • ⟨u, hXM (hHX hu)⟩ := rfl
        rw [h, map_smul, PIv_smul, hu0 o ho, mul_zero] }
  have hNH : N ≤ hull M (f₀ : Fn) := fun u hu => hu.1

  have hKS : ∀ (u : Fn) (hu : u ∈ hull M (f₀ : Fn)),
      (∀ o : Fin 3 → Fin 3 → ℝ, Orth o → PIv ε k₁ (Λ ⟨u, hXM (hHX hu)⟩) o = 0) → _ :=
    fun u hu hker =>
      LanglandsTunnell.CubicInduction.signProjection_read_kernel_stable_of_doubleSlotCoeffMap
        M ω h1 h3 h4 h5 h10 h11 h12 h13 N₂ a₂ ha₂ N₃ a₃ ha₃ hrel ρ n J e δ hδ he hre hexp i9 i9' j₀ j₀' ν Λ hΛa hΛb hΛc ε k₁ hk₁
        (hull M (f₀ : Fn)) (hHX.trans hXM) hHK hHD (fun u hu => hXeq u (hHX hu)) u hu hker
  have hNK : KSt N := by
    rintro u ⟨hu, hu0⟩ k hk1 hk2
    exact ⟨hHK u hu k hk1 hk2, (hKS u hu hu0).1 k hk1 hk2⟩
  have hND : DSt N := by
    rintro u ⟨hu, hu0⟩ i j
    exact ⟨hHD u hu i j, (hKS u hu hu0).2 i j⟩
  have hPN : ∀ w : ↥(hull M (f₀ : Fn)), (w : Fn) ∈ N → ((P w : ↥(hull M (f₀ : Fn))) : Fn) ∈ N := by
    intro w hwN
    exact span_trSet_le hNK hwN (hP1 ⟨(w : Fn), hHX w.2⟩)
  have hPP : ∀ w : ↥(hull M (f₀ : Fn)), P (P w) = P w := by
    intro w
    apply Subtype.ext
    show ((P₀ ⟨((P w : ↥(hull M (f₀ : Fn))) : Fn), hHX (P w).2⟩ : ↥X) : Fn) = ((P w : ↥(hull M (f₀ : Fn))) : Fn)
    have h : (⟨((P w : ↥(hull M (f₀ : Fn))) : Fn), hHX (P w).2⟩ : ↥X) = P₀ ⟨(w : Fn), hHX w.2⟩ :=
      Subtype.ext rfl
    rw [h, hP2]
    rfl
  have hPB : ∀ w w' : ↥(hull M (f₀ : Fn)), B (P w) w' = B w (P w') :=
    fun w w' => hP3 ⟨(w : Fn), hHX w.2⟩ ⟨(w' : Fn), hHX w'.2⟩
  have hPfin : FiniteDimensional ℂ ↥(LinearMap.range P) := by
    haveI := hEfin
    exact finite_range_of_forall_mem P E (fun u => hE _ (P u).2 (hP5 ⟨(u : Fn), hHX u.2⟩))
  have hPf : P ⟨(f₀ : Fn), hfH⟩ = ⟨(f₀ : Fn), hfH⟩ := by
    apply Subtype.ext
    show ((P₀ ⟨(f₀ : Fn), hHX hfH⟩ : ↥X) : Fn) = (f₀ : Fn)
    have h : (⟨(f₀ : Fn), hHX hfH⟩ : ↥X) = f₀ := Subtype.ext rfl
    rw [h, hf₀P]
  refine ⟨hull M (f₀ : Fn), hHX, hHK, hHD, N, hNH, hNK, hND, ?_, ?_, P, hPN, hPP, hPB, hPfin,
    ⟨(f₀ : Fn), hfH⟩, hPf, ?_⟩
  · intro u hu hker
    exact ⟨hu, hker⟩
  · rintro u ⟨hu, hu0⟩ o ho
    exact hu0 o ho
  · intro o ho
    exact hf₀read o ho

end CoreP47

end

theorem solution
    (M : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (h1 :
      (∀ w ∈ M, WhittakerBlock.IsArchSmooth3 w ∧
        WhittakerBlock.IsArchSmooth3
          (whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ w) ∧
        (∀ wd : List (Fin 3 × Fin 3),
          Continuous (List.foldr (fun ij ψ => WhittakerBlock.archDeriv ij.1 ij.2 ψ) w wd)) ∧
        ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), w (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = w g))
    (h3 :
      (∀ w ∈ M, ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))))
    (h4 :
      (∀ w ∈ M, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M))
    (h5 : (∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M))
    (h10 :
      (∃ B : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → ℂ,
        (∀ w ∈ M, ∀ w' ∈ M, B w' w = (starRingEnd ℂ) (B w w')) ∧
        (∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ w' ∈ M, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') ∧
        (∀ w ∈ M, w ≠ 0 → 0 < (B w w).re) ∧
        (∀ w ∈ M, ∀ w' ∈ M, ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w')) ∧
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ M, ∀ w' ∈ M, B (fun g => w (g * k)) (fun g => w' (g * k)) = B w w'))
    (h11 :
      (∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ M,
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l] w)) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0))
    (h12 :
      (∀ v ∈ M, ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        v (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * v g))
    (h13 :
      (∀ v ∈ M, ∃ N : ℕ, ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) v w g‖ ≤ C * gauge3 ℚ g ^ N))
    (N₂ : ℕ) (a₂ : Fin (N₂ + 1) → ℂ) (ha₂ : a₂ (Fin.last N₂) = 1)
    (N₃ : ℕ) (a₃ : Fin (N₃ + 1) → ℂ) (ha₃ : a₃ (Fin.last N₃) = 1)
    (hrel : ∀ w ∈ M,
      (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧ (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0)
    (ρ : ℝ) (n J : ℕ) (e : Fin n → ℂ) (δ : ℝ) (hδ : 0 < δ) (he : Function.Injective e)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hexp : ∀ (N : ℕ) (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
      (∀ w : List (Fin 3 × Fin 3), Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w)) →
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g) →
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g) →
      WhittakerBlock.IsArchSmooth3 u →
      (∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))) →
      (∑ m, a₂ m • (WhittakerBlock.casimir2^[m] u) = 0) →
      (∑ m, a₃ m • (WhittakerBlock.casimir3^[m] u) = 0) →
      (∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N) →
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ (ρ + δ)) ∧
        ∃ c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          (∀ i j i' j', Continuous (c' i j i' j')) ∧
          (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
            ‖c i j y₂ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₂ ^ (ρ + δ)) ∧
          (∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₂ : ℝ, 0 < y₂ → c i'' j'' y₂ k = 0) →
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i' : Fin n) (j' : Fin J), c' i j i' j' k = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₂ : ℝ), 0 < y₂ → c i j y₂ k = 0)) ∧
      (∃ c : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
        (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => c i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₁ : ℝ, b⁻¹ ≤ y₁ → y₁ ≤ b → ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin n, ∑ j : Fin J, c i j y₁ k * ((y₂ : ℂ) ^ e i * ((Real.log y₂ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₂ ^ (ρ + δ)) ∧
        ∃ c' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ,
          (∀ i j i' j', Continuous (c' i j i' j')) ∧
          (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
            ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
            ‖c i j y₁ k -
                (∑ i' : Fin n, ∑ j' : Fin J,
                  c' i j i' j' k * ((y₁ : ℂ) ^ e i' * ((Real.log y₁ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤
              C * y₁ ^ (ρ + δ)) ∧
          (∀ (i : Fin n) (j : Fin J),
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i'' : Fin n) (j'' : Fin J), (e i'').re < (e i).re →
              ∀ y₁ : ℝ, 0 < y₁ → c i'' j'' y₁ k = 0) →
            (∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i' : Fin n) (j' : Fin J), c' i j i' j' k = 0) →
            ∀ (k : AdelicGL 3 (𝓞 ℚ) ℚ) (y₁ : ℝ), 0 < y₁ → c i j y₁ k = 0)))
    (i9 i9' : Fin n) (j₀ j₀' : Fin J) (ν : Fin 3 → ℂ)
    (Λ : ↥M →ₗ[ℂ] (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (hΛa : (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M)
        (cv : Fin n → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
        (cv' : Fin n → Fin J → Fin n → Fin J → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ),
        ((∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => cv i j p.1 p.2) {p | 0 < p.1}) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
        ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
        ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
            NumberField.StandardAddChar.psiQ v
            (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
          (∑ i : Fin n, ∑ j : Fin J, cv i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
        C * y₁ ^ (ρ + δ)) ∧
        (∀ i j i' j', Continuous (cv' i j i' j')) ∧
        (∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∃ C : ℝ, ∀ k ∈ K, ∀ (i : Fin n) (j : Fin J),
        ∀ y₂ : ℝ, 0 < y₂ → y₂ ≤ 1 →
        ‖cv i j y₂ k - (∑ i' : Fin n, ∑ j' : Fin J, cv' i j i' j' k *
          ((y₂ : ℂ) ^ e i' * ((Real.log y₂ : ℝ) : ℂ) ^ (j' : ℕ)))‖ ≤ C * y₂ ^ (ρ + δ))) →
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, Λ ⟨v, hv⟩ k = cv' i9 j₀ i9' j₀' k))
    (hΛb : (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M) (k' : AdelicGL 3 (𝓞 ℚ) ℚ)
        (hk'₁ : ∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k' = 1)
        (hk'₂ : archComponent3 (𝓞 ℚ) ℚ k' ∈ orth3),
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
          Λ ⟨fun x => v (x * k'), h4 v hv k' hk'₁ hk'₂⟩ g = Λ ⟨v, hv⟩ (g * k')))
    (hΛc : (∀ (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : v ∈ M) (c d : Fin 3) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        HasDerivAt
          (fun s : ℝ => Λ ⟨v, hv⟩ (g * WhittakerBlock.archRealLift3 fun a b =>
            (if a = b then (1 : ℝ) else 0) + if a = c ∧ b = d then s else 0))
          (Λ ⟨WhittakerBlock.archDeriv c d v, h5 v hv c d⟩ g) 0))
    (ε : Fin 3 → Fin 2) (k₁ : AdelicGL 3 (𝓞 ℚ) ℚ) (hk₁ : archComponent3 (𝓞 ℚ) ℚ k₁ = 1)
    (ℓ : ℕ) (hℓ : ℓ = 0 ∨ ℓ = 1) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (X : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (hXM : X ≤ M) (hXK : ((∀ w ∈ X, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ X))) (hXD : ((∀ w ∈ X, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ X)))
    (hXeq : ∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u ∈ X), (∀ t : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, j < i → t i j = 0) → (∀ i : Fin 3, 0 < t i i) →
        ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, Λ ⟨u, hXM hu⟩ (WhittakerBlock.archRealLift3 t * g) =
          (∏ a : Fin 3, ((t a a : ℝ) : ℂ) ^ (ν a + (![1, 0, -1] : Fin 3 → ℂ) a)) * Λ ⟨u, hXM hu⟩ g))
    (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hvX : v ∈ X)
    (hvread : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨v, hXM hvX⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁))) =
        (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p)) :
    ∃ M' : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∃ hle : M' ≤ X, ((∀ w ∈ M', ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ M')) ∧ ((∀ w ∈ M', ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M')) ∧
      (∀ (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : u ∈ M'), (∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨u, hXM (hle hu)⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁))) = 0) → u = 0) ∧
      ∃ (v' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv' : v' ∈ M'), ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
        ((1 / 8 : ℂ) * ∑ τ : Fin 3 → Fin 2, (-1 : ℂ) ^ (∑ a : Fin 3, (ε a : ℕ) * (τ a : ℕ)) *
          Λ ⟨v', hXM (hle hv')⟩ (WhittakerBlock.archRealLift3 (fun a b => if a = b then (-1 : ℝ) ^ (τ a : ℕ) else 0) * (WhittakerBlock.archRealLift3 o * k₁))) =
          (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) := by
  obtain ⟨B, hB⟩ := h10

  have hBX : ((∀ w ∈ X, ∀ w' ∈ X, B w' w = (starRingEnd ℂ) (B w w')) ∧
        (∀ (z : ℂ), ∀ w₁ ∈ X, ∀ w₂ ∈ X, ∀ w' ∈ X, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') ∧
        (∀ w ∈ X, w ≠ 0 → 0 < (B w w).re) ∧
        (∀ w ∈ X, ∀ w' ∈ X, ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w')) ∧
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ X, ∀ w' ∈ X, B (fun g => w (g * k)) (fun g => w' (g * k)) = B w w') :=
    ⟨fun w hw w' hw' => hB.1 w (hXM hw) w' (hXM hw'),
     fun z w₁ hw₁ w₂ hw₂ w' hw' => hB.2.1 z w₁ (hXM hw₁) w₂ (hXM hw₂) w' (hXM hw'),
     fun w hw hw0 => hB.2.2.1 w (hXM hw) hw0,
     fun w hw w' hw' i j => hB.2.2.2.1 w (hXM hw) w' (hXM hw') i j,
     fun k hk1 hk2 w hw w' hw' => hB.2.2.2.2 k hk1 hk2 w (hXM hw) w' (hXM hw')⟩

  obtain ⟨P₀, hP1, hP2, hP3, hP4, hP5⟩ :=
    exists_isotypicProjector_natural_of_orthFinite_of_derivStable X hXD hXK (fun w hw => h3 w (hXM hw))
      (fun w hw => (h1 w (hXM hw)).2.2.1 []) (fun w hw => (h1 w (hXM hw)).1) B hBX
      ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) (Nat.mod_two_eq_zero_or_one _) ℓ hℓ

  have hnat := CoreS.Phi_natural M h4 Λ hΛb ε k₁ hk₁ X hXM hXK
  have hτ := CoreS.read_tauType M Λ ε k₁ X hXM ℓ hℓ p hp v hvX hvread
  have hf₀read : ∀ o : Fin 3 → Fin 3 → ℝ, (∀ i j : Fin 3, ∑ a : Fin 3, o a i * o a j = if i = j then 1 else 0) →
      CoreS.PIv ε k₁ (Λ ⟨((P₀ ⟨v, hvX⟩ : ↥X) : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), hXM (P₀ ⟨v, hvX⟩).2⟩) o =
        (Matrix.of fun i j : Fin 3 => ((o i j : ℝ) : ℂ)).det ^ ((ℓ + ∑ a : Fin 3, (ε a : ℕ)) % 2) *
          MvPolynomial.eval (fun ij : Fin 3 × Fin 3 => ((o ij.1 ij.2 : ℝ) : ℂ)) (MvPolynomial.aeval (fun a : Fin 3 => (MvPolynomial.X (a, 0) : MvPolynomial (Fin 3 × Fin 3) ℂ)) p) := by
    intro o ho
    have h := hP4 _ hnat ⟨v, hvX⟩ hτ o ho
    rw [← hvread o ho]
    exact h
  obtain ⟨H, hHX, hHK, hHD, N, hNH, hNK, hND, hNin, hNout, P, hPN, hPP, hPB, hPfin, f, hPf, hfread⟩ :=
    CoreP47.PROJDATA_of_P123 M ω h1 h3 h4 h5 ⟨B, hB⟩ h11 h12 h13 N₂ a₂ ha₂ N₃ a₃ ha₃ hrel ρ n J e δ hδ he hre hexp i9 i9' j₀ j₀' ν Λ hΛa hΛb hΛc ε k₁ hk₁ ℓ hℓ p hp X hXM hXK hXD hXeq
      v hvX hvread B hB ⟨P₀, hP1, hP2, hP3, hP5, P₀ ⟨v, hvX⟩, hP2 _, hf₀read⟩
  have hHM : H ≤ M := fun u hu => hXM (hHX hu)
  have hBH : ((∀ w ∈ H, ∀ w' ∈ H, B w' w = (starRingEnd ℂ) (B w w')) ∧
        (∀ (z : ℂ), ∀ w₁ ∈ H, ∀ w₂ ∈ H, ∀ w' ∈ H, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w') ∧
        (∀ w ∈ H, w ≠ 0 → 0 < (B w w).re) ∧
        (∀ w ∈ H, ∀ w' ∈ H, ∀ i j : Fin 3,
          B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w')) ∧
        ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
            ∀ w ∈ H, ∀ w' ∈ H, B (fun g => w (g * k)) (fun g => w' (g * k)) = B w w') :=
    ⟨fun w hw w' hw' => hB.1 w (hHM hw) w' (hHM hw'),
     fun z w₁ hw₁ w₂ hw₂ w' hw' => hB.2.1 z w₁ (hHM hw₁) w₂ (hHM hw₂) w' (hHM hw'),
     fun w hw hw0 => hB.2.2.1 w (hHM hw) hw0,
     fun w hw w' hw' i j => hB.2.2.2.1 w (hHM hw) w' (hHM hw') i j,
     fun k hk1 hk2 w hw w' hw' => hB.2.2.2.2 k hk1 hk2 w (hHM hw) w' (hHM hw')⟩
  obtain ⟨M', hM'H, hK', hD', hinf, v', hv', hfv'⟩ :=
    exists_stable_submodule_inf_eq_bot_and_sub_mem_of_positive_skew_form H N hNH hHK hHD hNK hND B hBH P hPN hPP hPB
      hPfin f hPf
  refine ⟨M', fun u hu => hHX (hM'H hu), hK', hD', ?_, v', hv', ?_⟩
  · intro u hu hu0
    have huN : u ∈ N := hNin u (hM'H hu) hu0
    have : u ∈ M' ⊓ N := ⟨hu, huN⟩
    rw [hinf] at this
    exact (Submodule.mem_bot ℂ).1 this
  · intro o ho
    have h1 := hNout _ hfv' o ho
    have h2 := hfread o ho
    have hsub : (Λ ⟨(f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - v', hXM (hHX (hNH hfv'))⟩ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) =
        (Λ ⟨(f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), hXM (hHX f.2)⟩ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) - Λ ⟨v', hXM (hHX (hM'H hv'))⟩ := by
      rw [← map_sub]; rfl
    have hsub' : ∀ F G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, CoreP47.PIv ε k₁ (F - G) o = CoreP47.PIv ε k₁ F o - CoreP47.PIv ε k₁ G o := by
      intro F G; simp only [CoreP47.PIv, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hsub, hsub', sub_eq_zero] at h1
    rw [h1] at h2
    exact h2

end S_LanglandsTunnell_CubicInduction_exists_separating_stable_submodule_of_equivariant_stable_submodule
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_separating_stable_submodule_of_equivariant_stable_submodule (solution)
