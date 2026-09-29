-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_finiteDimensional_forall_mem_hull_of_rotationType_of_smoothingSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/e46dee57-f672-51be-8c15-92902d4ab286

import Definitions.Def_LanglandsTunnell_CubicInduction_KFinite3
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Theorems.Thm_LanglandsTunnell_CubicInduction_archDeriv_comp_mul_right_eq_sum_realMat_of_isArchSmooth3
import Theorems.Thm_LanglandsTunnell_CubicInduction_isArchSmooth3_mul_right
import Theorems.Thm_LanglandsTunnell_CubicInduction_componentAt3_archRealLift3_eq_one_and_realMat_archComponent3_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3
import Theorems.Thm_LanglandsTunnell_CubicInduction_finiteDimensional_invariants_gKSpan_of_isCentreFinite
import Theorems.Thm_LanglandsTunnell_CubicInduction_finiteDimensional_ker_rotationCasimir_add_two_gKSpan_of_isCentreFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_finiteDimensional_forall_mem_hull_of_rotationType_of_smoothingSubmodule
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level"

set_option autoImplicit false

attribute [local instance 100] LieRing.ofAssociativeRing

open IsDedekindDomain NumberField AutomorphicForm Topology Filter
open LanglandsTunnell.CubicInduction
open scoped LanglandsTunnell.CubicInduction.WhittakerBlock

noncomputable section

namespace WsF
namespace CA

abbrev E33 : Type := Fin 3 → Fin 3 → ℝ
abbrev G3 : Type := AdelicGL 3 (𝓞 ℚ) ℚ

def RM (k : G3) : Matrix (Fin 3) (Fin 3) ℝ := AutomorphicForm.StandardKernel.realMat (archComponent3 (𝓞 ℚ) ℚ k)

def one33 : E33 := fun a b => if a = b then 1 else 0

theorem archDeriv_translate (φ : G3 → ℂ) (hφ : WhittakerBlock.IsArchSmooth3 φ) (k : G3) (i j : Fin 3) (g : G3) :
    WhittakerBlock.archDeriv i j (fun x => φ (x * k)) g =
      ∑ a : Fin 3, ∑ b : Fin 3, ((RM k)⁻¹ a i * RM k j b : ℝ) • WhittakerBlock.archDeriv a b φ (g * k) := by
  rw [LanglandsTunnell.CubicInduction.archDeriv_comp_mul_right_eq_sum_realMat_of_isArchSmooth3 φ hφ k i j g]
  simp only [Complex.real_smul]
  rfl

theorem isArchSmooth3_translate (φ : G3 → ℂ) (hφ : WhittakerBlock.IsArchSmooth3 φ) (k : G3) :
    WhittakerBlock.IsArchSmooth3 (fun x => φ (x * k)) :=
  LanglandsTunnell.CubicInduction.isArchSmooth3_mul_right φ hφ k

end WsF.CA

namespace WsF
namespace CA

def Rsm (k : G3) : WhittakerBlock.smoothFunctions3 →ₗ[ℂ] WhittakerBlock.smoothFunctions3 where
  toFun φ := ⟨fun x => (φ : G3 → ℂ) (x * k), isArchSmooth3_translate _ φ.2 k⟩
  map_add' φ ψ := rfl
  map_smul' c φ := rfl

theorem coe_Rsm (k : G3) (φ : WhittakerBlock.smoothFunctions3) :
    ((Rsm k φ : WhittakerBlock.smoothFunctions3) : G3 → ℂ) = fun x => (φ : G3 → ℂ) (x * k) := rfl

theorem RM_col (k : G3) (hk : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) (a c : Fin 3) :
    (∑ i : Fin 3, RM k i a * RM k i c) = if a = c then 1 else 0 := by
  have h : (RM k).transpose * RM k = 1 := AutomorphicForm.StandardKernel.realMat_orth hk
  have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M a c) h
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using this

theorem RM_inv (k : G3) (hk : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) : (RM k)⁻¹ = (RM k).transpose :=
  Matrix.inv_eq_left_inv (AutomorphicForm.StandardKernel.realMat_orth hk)

theorem RM_row (k : G3) (hk : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) (a c : Fin 3) :
    (∑ i : Fin 3, RM k a i * RM k c i) = if a = c then 1 else 0 := by
  have h1 : (RM k).transpose * RM k = 1 := AutomorphicForm.StandardKernel.realMat_orth hk
  have h : RM k * (RM k).transpose = 1 := mul_eq_one_comm.mp h1
  have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M a c) h
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using this

theorem archDerivₗ_Rsm (k : G3) (hk : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) (i j : Fin 3) (φ : WhittakerBlock.smoothFunctions3) :
    WhittakerBlock.archDerivₗ i j (Rsm k φ) =
      ∑ a : Fin 3, ∑ b : Fin 3, ((RM k i a * RM k j b : ℝ) : ℂ) • Rsm k (WhittakerBlock.archDerivₗ a b φ) := by
  apply Subtype.ext
  funext g
  have h := archDeriv_translate (φ : G3 → ℂ) φ.2 k i j g
  rw [RM_inv k hk] at h
  simp only [Matrix.transpose_apply, Complex.real_smul] at h
  rw [WhittakerBlock.coe_archDerivₗ_apply, coe_Rsm, h]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, coe_Rsm,
    WhittakerBlock.coe_archDerivₗ_apply]

theorem sum_pair_collapse {W : Type*} [AddCommMonoid W] [Module ℂ W] (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hcol : ∀ a c : Fin 3, (∑ i : Fin 3, R i a * R i c) = if a = c then 1 else 0)
    (Q : Fin 3 × Fin 3 → W) (p : Fin 3 × Fin 3) :
    (∑ q : Fin 3 × Fin 3, ((R q.1 p.1 * R q.2 p.2 : ℝ) : ℂ) •
        ∑ p' : Fin 3 × Fin 3, ((R q.1 p'.1 * R q.2 p'.2 : ℝ) : ℂ) • Q p') = Q p := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have key : ∀ p' : Fin 3 × Fin 3,
      (∑ q : Fin 3 × Fin 3, ((R q.1 p.1 * R q.2 p.2 : ℝ) : ℂ) * ((R q.1 p'.1 * R q.2 p'.2 : ℝ) : ℂ)) =
        if p' = p then 1 else 0 := by
    intro p'
    have e1 : (∑ q : Fin 3 × Fin 3, ((R q.1 p.1 * R q.2 p.2 : ℝ) : ℂ) * ((R q.1 p'.1 * R q.2 p'.2 : ℝ) : ℂ)) =
        (((∑ i : Fin 3, R i p.1 * R i p'.1) * (∑ j : Fin 3, R j p.2 * R j p'.2) : ℝ) : ℂ) := by
      push_cast
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      simp only [Finset.univ_product_univ]
      refine Finset.sum_congr rfl (fun q _ => by ring)
    rw [e1, hcol, hcol]
    rcases p with ⟨a, b⟩
    rcases p' with ⟨c, d⟩
    by_cases hac : a = c <;> by_cases hbd : b = d <;> simp [hac, hbd, eq_comm]
  simp only [key]
  rw [Fintype.sum_eq_single p (fun p' hp' => by rw [if_neg hp', zero_smul])]
  simp

theorem Rsm_archDerivₗ (k : G3) (hk : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) (a b : Fin 3) (φ : WhittakerBlock.smoothFunctions3) :
    Rsm k (WhittakerBlock.archDerivₗ a b φ) =
      ∑ i : Fin 3, ∑ j : Fin 3, ((RM k i a * RM k j b : ℝ) : ℂ) • WhittakerBlock.archDerivₗ i j (Rsm k φ) := by
  simp only [archDerivₗ_Rsm k hk]
  have := sum_pair_collapse (RM k) (RM_col k hk) (fun p' => Rsm k (WhittakerBlock.archDerivₗ p'.1 p'.2 φ)) (a, b)
  simp only [Fintype.sum_prod_type] at this
  exact this.symm

end WsF.CA

namespace WsF
namespace CA

def Lr (i j : Fin 3) : Module.End ℂ WhittakerBlock.smoothFunctions3 :=
  WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1)

theorem Lr_eq (i j : Fin 3) : Lr i j = WhittakerBlock.archDerivₗ i j - WhittakerBlock.archDerivₗ j i := by
  rw [Lr, map_sub, WhittakerBlock.derivAction3_single, WhittakerBlock.derivAction3_single]

theorem Lr_apply (i j : Fin 3) (φ : WhittakerBlock.smoothFunctions3) :
    Lr i j φ = WhittakerBlock.archDerivₗ i j φ - WhittakerBlock.archDerivₗ j i φ := by
  rw [Lr_eq]; rfl

def Om : Module.End ℂ WhittakerBlock.smoothFunctions3 :=
  Lr 0 1 * Lr 0 1 + Lr 0 2 * Lr 0 2 + Lr 1 2 * Lr 1 2

theorem Om_apply (φ : WhittakerBlock.smoothFunctions3) : Om φ = ∑ a : Fin 3, ∑ b : Fin 3,
    (WhittakerBlock.archDerivₗ a b (WhittakerBlock.archDerivₗ a b φ) -
      WhittakerBlock.archDerivₗ a b (WhittakerBlock.archDerivₗ b a φ)) := by
  simp only [Om, LinearMap.add_apply, Module.End.mul_apply, Lr_apply, map_sub, Fin.sum_univ_three]
  abel

theorem Lr_Rsm (k : G3) (hk : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) (i j : Fin 3) (φ : WhittakerBlock.smoothFunctions3) :
    Lr i j (Rsm k φ) = ∑ a : Fin 3, ∑ b : Fin 3, ((RM k i a * RM k j b : ℝ) : ℂ) • Rsm k (Lr a b φ) := by
  simp only [Lr_apply, archDerivₗ_Rsm k hk, map_sub, smul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp only [mul_comm (RM k j _) (RM k i _)]

theorem Rsm_Lr (k : G3) (hk : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) (a b : Fin 3) (φ : WhittakerBlock.smoothFunctions3) :
    Rsm k (Lr a b φ) = ∑ i : Fin 3, ∑ j : Fin 3, ((RM k i a * RM k j b : ℝ) : ℂ) • Lr i j (Rsm k φ) := by
  simp only [Lr_apply, map_sub, Rsm_archDerivₗ k hk, smul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp only [mul_comm (RM k _ b) (RM k _ a)]

theorem sum_pair_collapse₂ {W : Type*} [AddCommMonoid W] [Module ℂ W] (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hcol : ∀ a c : Fin 3, (∑ i : Fin 3, R i a * R i c) = if a = c then 1 else 0)
    (Q : Fin 3 × Fin 3 → Fin 3 × Fin 3 → W) :
    (∑ q : Fin 3 × Fin 3, ∑ p' : Fin 3 × Fin 3, ((R q.1 p'.1 * R q.2 p'.2 : ℝ) : ℂ) •
        ∑ p'' : Fin 3 × Fin 3, ((R q.1 p''.1 * R q.2 p''.2 : ℝ) : ℂ) • Q p'' p') =
      ∑ p : Fin 3 × Fin 3, Q p p := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have key : ∀ p' p'' : Fin 3 × Fin 3,
      (∑ q : Fin 3 × Fin 3, ((R q.1 p'.1 * R q.2 p'.2 : ℝ) : ℂ) * ((R q.1 p''.1 * R q.2 p''.2 : ℝ) : ℂ)) =
        if p'' = p' then 1 else 0 := by
    intro p' p''
    have e1 : (∑ q : Fin 3 × Fin 3, ((R q.1 p'.1 * R q.2 p'.2 : ℝ) : ℂ) * ((R q.1 p''.1 * R q.2 p''.2 : ℝ) : ℂ)) =
        (((∑ i : Fin 3, R i p'.1 * R i p''.1) * (∑ j : Fin 3, R j p'.2 * R j p''.2) : ℝ) : ℂ) := by
      push_cast
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      simp only [Finset.univ_product_univ]
      refine Finset.sum_congr rfl (fun q _ => by ring)
    rw [e1, hcol, hcol]
    rcases p' with ⟨a, b⟩
    rcases p'' with ⟨c, d⟩
    by_cases hac : a = c <;> by_cases hbd : b = d <;> simp [hac, hbd, eq_comm]
  refine Finset.sum_congr rfl (fun p' _ => ?_)
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, key]
  rw [Fintype.sum_eq_single p' (fun p'' hp'' => by rw [if_neg hp'', zero_smul])]
  simp

theorem Om_Rsm (k : G3) (hk : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) (φ : WhittakerBlock.smoothFunctions3) :
    Om (Rsm k φ) = Rsm k (Om φ) := by
  rw [Om_apply, Om_apply]
  simp only [map_sum, map_sub]

  have h2 : ∀ a b c d : Fin 3, WhittakerBlock.archDerivₗ a b (WhittakerBlock.archDerivₗ c d (Rsm k φ)) =
      ∑ c' : Fin 3, ∑ d' : Fin 3, ((RM k c c' * RM k d d' : ℝ) : ℂ) •
        ∑ a' : Fin 3, ∑ b' : Fin 3, ((RM k a a' * RM k b b' : ℝ) : ℂ) •
          Rsm k (WhittakerBlock.archDerivₗ a' b' (WhittakerBlock.archDerivₗ c' d' φ)) := by
    intro a b c d
    rw [archDerivₗ_Rsm k hk c d]
    simp only [map_sum, map_smul, archDerivₗ_Rsm k hk a b]
  simp only [h2]
  simp only [Finset.sum_sub_distrib]
  congr 1
  ·
    have := sum_pair_collapse₂ (RM k) (RM_col k hk)
      (fun p'' p' => Rsm k (WhittakerBlock.archDerivₗ p''.1 p''.2 (WhittakerBlock.archDerivₗ p'.1 p'.2 φ)))
    simp only [Fintype.sum_prod_type] at this
    exact this
  ·
    have := sum_pair_collapse₂ (RM k) (RM_col k hk)
      (fun p'' p' => Rsm k (WhittakerBlock.archDerivₗ p''.1 p''.2 (WhittakerBlock.archDerivₗ p'.2 p'.1 φ)))
    simp only [Fintype.sum_prod_type] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ => ?_))
    rw [mul_comm]

end WsF.CA

namespace WsF
namespace CA

def IsK (k : G3) : Prop :=
  (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) ∧ archComponent3 (𝓞 ℚ) ℚ k ∈ orth3

theorem isK_mul {k k' : G3} (hk : IsK k) (hk' : IsK k') : IsK (k * k') := by
  refine ⟨fun p => by rw [map_mul, hk.1 p, hk'.1 p, one_mul], ?_⟩
  have h1 : ((archComponent3 (𝓞 ℚ) ℚ k : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
      Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose * (archComponent3 (𝓞 ℚ) ℚ k) = 1 := hk.2
  have h2 : ((archComponent3 (𝓞 ℚ) ℚ k' : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
      Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose * (archComponent3 (𝓞 ℚ) ℚ k') = 1 := hk'.2
  show ((archComponent3 (𝓞 ℚ) ℚ (k * k') : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
      Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose * (archComponent3 (𝓞 ℚ) ℚ (k * k')) = 1
  rw [map_mul, Units.val_mul, Matrix.transpose_mul]
  set A : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) :=
    ((archComponent3 (𝓞 ℚ) ℚ k : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
  set B : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) :=
    ((archComponent3 (𝓞 ℚ) ℚ k' : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
  rw [show B.transpose * A.transpose * (A * B) = B.transpose * ((A.transpose * A) * B) by
    simp only [Matrix.mul_assoc], h1, Matrix.one_mul, h2]

theorem isK_one : IsK 1 := by
  refine ⟨fun p => map_one _, ?_⟩
  show ((archComponent3 (𝓞 ℚ) ℚ 1 : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
      Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)).transpose * (archComponent3 (𝓞 ℚ) ℚ 1) = 1
  rw [map_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul]

theorem isK_lift {e : E33} (he : (Matrix.of e).det ≠ 0)
    (ho : ∀ i j : Fin 3, ∑ a : Fin 3, e a i * e a j = if i = j then 1 else 0) :
    IsK (WhittakerBlock.archRealLift3 e) := by
  have h := LanglandsTunnell.CubicInduction.componentAt3_archRealLift3_eq_one_and_realMat_archComponent3_eq e he
  exact ⟨h.1, h.2.2 ho⟩

def Rf (k : G3) : (G3 → ℂ) →ₗ[ℂ] (G3 → ℂ) where
  toFun u := fun g => u (g * k)
  map_add' u v := rfl
  map_smul' c u := rfl

theorem Rf_apply (k : G3) (u : G3 → ℂ) : Rf k u = fun g => u (g * k) := rfl

theorem Rf_mul (k k' : G3) (u : G3 → ℂ) : Rf k (Rf k' u) = Rf (k * k') u := by
  funext g; simp [Rf_apply, mul_assoc]

theorem Rf_one (u : G3 → ℂ) : Rf 1 u = u := by
  funext g; simp [Rf_apply]

theorem coe_Rsm' (k : G3) (φ : WhittakerBlock.smoothFunctions3) :
    ((Rsm k φ : WhittakerBlock.smoothFunctions3) : G3 → ℂ) = Rf k (φ : G3 → ℂ) := rfl

theorem translate_mem_orthSpan (f : G3 → ℂ) {k : G3} (hk : IsK k) : Rf k f ∈ WhittakerBlock.orthSpan f :=
  Submodule.subset_span ⟨k, hk.1, hk.2, rfl⟩

theorem self_mem_orthSpan (f : G3 → ℂ) : f ∈ WhittakerBlock.orthSpan f := by
  have := translate_mem_orthSpan f isK_one
  rwa [Rf_one] at this

theorem orthSpan_le {f : G3 → ℂ} {M : Submodule ℂ (G3 → ℂ)} (hf : f ∈ M)
    (h4 : ∀ w ∈ M, ∀ k : G3, IsK k → Rf k w ∈ M) : WhittakerBlock.orthSpan f ≤ M := by
  refine Submodule.span_le.mpr ?_
  rintro φ ⟨k, hk1, hk2, rfl⟩
  exact h4 f hf k ⟨hk1, hk2⟩

theorem orthSpan_translate (f : G3 → ℂ) {k : G3} (hk : IsK k) {u : G3 → ℂ}
    (hu : u ∈ WhittakerBlock.orthSpan f) : Rf k u ∈ WhittakerBlock.orthSpan f := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k', hk1, hk2, rfl⟩ := hx
    rw [← Rf_apply k', Rf_mul]
    exact translate_mem_orthSpan f (isK_mul hk ⟨hk1, hk2⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem derivAction3_eq_sum (X : Matrix (Fin 3) (Fin 3) ℂ) :
    WhittakerBlock.derivAction3 X = ∑ i : Fin 3, ∑ j : Fin 3, X i j • WhittakerBlock.archDerivₗ i j := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, WhittakerBlock.derivAction3_single]

theorem envelopingHom3_coe_mem (M : Submodule ℂ (G3 → ℂ))
    (h5 : ∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M)
    (u : WhittakerBlock.envelopingAlgebra3) (φ : WhittakerBlock.smoothFunctions3) (hφ : (φ : G3 → ℂ) ∈ M) :
    ((WhittakerBlock.envelopingHom3 u φ : WhittakerBlock.smoothFunctions3) : G3 → ℂ) ∈ M := by
  have hsurj : Function.Surjective (UniversalEnvelopingAlgebra.mkAlgHom ℂ (Matrix (Fin 3) (Fin 3) ℂ)) :=
    RingCon.mkₐ_surjective _
  obtain ⟨t, rfl⟩ := hsurj u
  induction t using TensorAlgebra.induction generalizing φ with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, Submodule.coe_smul]
    exact M.smul_mem r hφ
  | ι X =>
    have hι : (UniversalEnvelopingAlgebra.mkAlgHom ℂ (Matrix (Fin 3) (Fin 3) ℂ))
        (TensorAlgebra.ι ℂ X) = UniversalEnvelopingAlgebra.ι ℂ X := rfl
    rw [hι, WhittakerBlock.envelopingHom3_ι, derivAction3_eq_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
      WhittakerBlock.coe_archDerivₗ_apply]
    exact Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => M.smul_mem _ (h5 _ hφ i j)))
  | mul a b ha hb =>
    rw [map_mul, map_mul, Module.End.mul_apply]
    exact ha _ (hb _ hφ)
  | add a b ha hb =>
    rw [map_add, map_add, LinearMap.add_apply, Submodule.coe_add]
    exact M.add_mem (ha _ hφ) (hb _ hφ)

def Msm (M : Submodule ℂ (G3 → ℂ)) (h5 : ∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M) :
    Submodule WhittakerBlock.envelopingAlgebra3 WhittakerBlock.smoothFunctions3 where
  carrier := {φ | (φ : G3 → ℂ) ∈ M}
  zero_mem' := by simp
  add_mem' := by
    intro φ ψ hφ hψ
    simp only [Set.mem_setOf_eq, Submodule.coe_add] at *
    exact M.add_mem hφ hψ
  smul_mem' := by
    intro u φ hφ
    show ((WhittakerBlock.envelopingHom3 u φ : WhittakerBlock.smoothFunctions3) : G3 → ℂ) ∈ M
    exact envelopingHom3_coe_mem M h5 u φ hφ

theorem mem_Msm {M : Submodule ℂ (G3 → ℂ)} {h5 : ∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M}
    {φ : WhittakerBlock.smoothFunctions3} : φ ∈ Msm M h5 ↔ (φ : G3 → ℂ) ∈ M := Iff.rfl

theorem gKSpan_le_Msm {f : G3 → ℂ} {M : Submodule ℂ (G3 → ℂ)} (hf : f ∈ M)
    (h4 : ∀ w ∈ M, ∀ k : G3, IsK k → Rf k w ∈ M)
    (h5 : ∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M) :
    WhittakerBlock.gKSpan f ≤ Msm M h5 := by
  refine Submodule.span_le.mpr ?_
  intro φ hφ
  exact orthSpan_le hf h4 hφ

theorem coe_mem_of_mem_gKSpan {f : G3 → ℂ} {M : Submodule ℂ (G3 → ℂ)} (hf : f ∈ M)
    (h4 : ∀ w ∈ M, ∀ k : G3, IsK k → Rf k w ∈ M)
    (h5 : ∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M)
    {φ : WhittakerBlock.smoothFunctions3} (hφ : φ ∈ WhittakerBlock.gKSpan f) : (φ : G3 → ℂ) ∈ M :=
  gKSpan_le_Msm hf h4 h5 hφ

theorem archDerivₗ_mem_gKSpan {f : G3 → ℂ} {φ : WhittakerBlock.smoothFunctions3}
    (hφ : φ ∈ WhittakerBlock.gKSpan f) (i j : Fin 3) :
    WhittakerBlock.archDerivₗ i j φ ∈ WhittakerBlock.gKSpan f := by
  have := (WhittakerBlock.gKSpan f).smul_mem (UniversalEnvelopingAlgebra.ι ℂ (Matrix.single i j (1 : ℂ))) hφ
  have h : (UniversalEnvelopingAlgebra.ι ℂ (Matrix.single i j (1 : ℂ))) • φ = WhittakerBlock.archDerivₗ i j φ := by
    show WhittakerBlock.envelopingHom3 (UniversalEnvelopingAlgebra.ι ℂ (Matrix.single i j (1 : ℂ))) φ = _
    rw [WhittakerBlock.envelopingHom3_ι, WhittakerBlock.derivAction3_single]
  rwa [h] at this

theorem smul_mem_gKSpan {f : G3 → ℂ} {φ : WhittakerBlock.smoothFunctions3}
    (hφ : φ ∈ WhittakerBlock.gKSpan f) (c : ℂ) : c • φ ∈ WhittakerBlock.gKSpan f := by
  have := (WhittakerBlock.gKSpan f).smul_mem (algebraMap ℂ WhittakerBlock.envelopingAlgebra3 c) hφ
  rwa [algebraMap_smul] at this

end WsF.CA

namespace WsF
namespace CA

theorem isCentreFinite_of_mem {M : Submodule ℂ (G3 → ℂ)}
    (h11 : ∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ M,
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l] w)) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0)
    {u : G3 → ℂ} (hu : u ∈ M) : WhittakerBlock.IsCentreFinite u := by
  obtain ⟨N₁, N₂, N₃, a₁, a₂, a₃, h₁, h₂, h₃, h⟩ := h11
  obtain ⟨r₁, r₂, r₃⟩ := h u hu
  exact ⟨⟨N₁, a₁, h₁, r₁⟩, ⟨N₂, a₂, h₂, r₂⟩, ⟨N₃, a₃, h₃, r₃⟩⟩

def rot (c₁ c₂ : Fin 3) (s : ℝ) : E33 := fun i j =>
  if i = c₁ ∧ j = c₁ then Real.cos s else if i = c₂ ∧ j = c₂ then Real.cos s else
  if i = c₁ ∧ j = c₂ then - Real.sin s else if i = c₂ ∧ j = c₁ then Real.sin s else
  if i = j then 1 else 0

theorem rot_colOrth (c₁ c₂ : Fin 3) (h : c₁ ≠ c₂) (s : ℝ) :
    ∀ i j : Fin 3, (∑ a : Fin 3, rot c₁ c₂ s a i * rot c₁ c₂ s a j) = if i = j then 1 else 0 := by
  intro i j
  have hsc := Real.sin_sq_add_cos_sq s
  fin_cases c₁ <;> fin_cases c₂ <;> (first | exact absurd rfl h | skip) <;>
    fin_cases i <;> fin_cases j <;> simp [rot, Fin.sum_univ_three] <;>
    (first | linear_combination hsc | linear_combination (-1 : ℝ) * hsc | ring1)

theorem det_ne_zero_of_colOrth' (r : E33)
    (ho : ∀ i j : Fin 3, (∑ a : Fin 3, r a i * r a j) = if i = j then 1 else 0) : (Matrix.of r).det ≠ 0 := by
  have h1 : (Matrix.of r).transpose * Matrix.of r = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Matrix.transpose_apply] using ho i j
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h2
  intro h0
  rw [h0, mul_zero] at h2
  exact zero_ne_one h2

theorem isK_lift_rot (c₁ c₂ : Fin 3) (h : c₁ ≠ c₂) (s : ℝ) : IsK (WhittakerBlock.archRealLift3 (rot c₁ c₂ s)) :=
  isK_lift (det_ne_zero_of_colOrth' _ (rot_colOrth c₁ c₂ h s)) (rot_colOrth c₁ c₂ h s)

theorem rot_zero (c₁ c₂ : Fin 3) : rot c₁ c₂ 0 = one33 := by
  funext a b
  simp only [rot, one33, Real.cos_zero, Real.sin_zero, neg_zero]
  by_cases h1 : a = c₁ ∧ b = c₁
  · rw [if_pos h1, if_pos (h1.1.trans h1.2.symm)]
  rw [if_neg h1]
  by_cases h2 : a = c₂ ∧ b = c₂
  · rw [if_pos h2, if_pos (h2.1.trans h2.2.symm)]
  rw [if_neg h2]
  by_cases h3 : a = c₁ ∧ b = c₂
  · rw [if_pos h3]
    by_cases hab : a = b
    · exact absurd ⟨h3.1, hab.symm.trans h3.1⟩ h1
    · rw [if_neg hab]
  rw [if_neg h3]
  by_cases h4 : a = c₂ ∧ b = c₁
  · rw [if_pos h4]
    by_cases hab : a = b
    · exact absurd ⟨h4.1, hab.symm.trans h4.1⟩ h2
    · rw [if_neg hab]
  rw [if_neg h4]

theorem finiteDimensional_orthSpan (f : G3 → ℂ) (hfin : WhittakerBlock.IsOrthFinite f) :
    FiniteDimensional ℂ (WhittakerBlock.orthSpan f) := by
  obtain ⟨s, hs⟩ := hfin
  have hle : WhittakerBlock.orthSpan f ≤ Submodule.span ℂ (s : Set (G3 → ℂ)) := by
    refine Submodule.span_le.mpr ?_
    rintro φ ⟨k, hk1, hk2, rfl⟩
    exact hs k hk1 hk2
  exact Submodule.finiteDimensional_of_le hle

theorem Lr_coe_mem_orthSpan (f : G3 → ℂ) (hfin : WhittakerBlock.IsOrthFinite f) (i j : Fin 3)
    (φ : WhittakerBlock.smoothFunctions3) (hφ : (φ : G3 → ℂ) ∈ WhittakerBlock.orthSpan f) :
    ((Lr i j φ : WhittakerBlock.smoothFunctions3) : G3 → ℂ) ∈ WhittakerBlock.orthSpan f := by
  by_cases hij : i = j
  · subst hij
    have : Lr i i φ = 0 := by rw [Lr_apply, sub_self]
    rw [this, Submodule.coe_zero]
    exact Submodule.zero_mem _
  haveI := finiteDimensional_orthSpan f hfin
  set V : Submodule ℂ (G3 → ℂ) := WhittakerBlock.orthSpan f with hV
  have hclosed : IsClosed (V : Set (G3 → ℂ)) := V.closed_of_finiteDimensional

  have hji : j ≠ i := fun h => hij h.symm
  let D : ℝ → (G3 → ℂ) := fun s => (s - 0)⁻¹ • (Rf (WhittakerBlock.archRealLift3 (rot j i s)) (φ : G3 → ℂ) -
    Rf (WhittakerBlock.archRealLift3 (rot j i 0)) (φ : G3 → ℂ))
  have hDmem : ∀ s, D s ∈ V := fun s => by
    simp only [D]
    rw [← Complex.coe_smul]
    exact V.smul_mem _ (V.sub_mem (orthSpan_translate f (isK_lift_rot j i hji s) hφ)
      (orthSpan_translate f (isK_lift_rot j i hji 0) hφ))
  have hlim : Tendsto D (𝓝[≠] 0) (𝓝 ((Lr i j φ : WhittakerBlock.smoothFunctions3) : G3 → ℂ)) := by
    rw [tendsto_pi_nhds]
    intro g
    have hrot := LanglandsTunnell.CubicInduction.WhittakerBlock.hasDerivAt_comp_archRealLift3_rotation_of_isArchSmooth3
      (φ : G3 → ℂ) φ.2 j i g
    have hslope := (hasDerivAt_iff_tendsto_slope.mp hrot)
    have hval : ((Lr i j φ : WhittakerBlock.smoothFunctions3) : G3 → ℂ) g =
        WhittakerBlock.archDeriv i j (φ : G3 → ℂ) g - WhittakerBlock.archDeriv j i (φ : G3 → ℂ) g := by
      rw [Lr_apply, Submodule.coe_sub, Pi.sub_apply, WhittakerBlock.coe_archDerivₗ_apply,
        WhittakerBlock.coe_archDerivₗ_apply]
    rw [hval]
    refine hslope.congr (fun s => ?_)
    simp only [slope, vsub_eq_sub, D, Pi.smul_apply, Pi.sub_apply, Rf_apply]
    try rfl
  exact hclosed.mem_of_tendsto hlim (Eventually.of_forall hDmem)

end WsF.CA

namespace WsF
namespace CA

def OmE : Module.End ℂ WhittakerBlock.smoothFunctions3 := Om + (2 : ℂ) • (1 : Module.End ℂ WhittakerBlock.smoothFunctions3)

def OmFun (u : G3 → ℂ) : G3 → ℂ :=
  (WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 0 1 u - WhittakerBlock.archDeriv 1 0 u) - WhittakerBlock.archDeriv 1 0 (WhittakerBlock.archDeriv 0 1 u - WhittakerBlock.archDeriv 1 0 u)) +
  (WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 0 2 u - WhittakerBlock.archDeriv 2 0 u) - WhittakerBlock.archDeriv 2 0 (WhittakerBlock.archDeriv 0 2 u - WhittakerBlock.archDeriv 2 0 u)) +
  (WhittakerBlock.archDeriv 1 2 (WhittakerBlock.archDeriv 1 2 u - WhittakerBlock.archDeriv 2 1 u) - WhittakerBlock.archDeriv 2 1 (WhittakerBlock.archDeriv 1 2 u - WhittakerBlock.archDeriv 2 1 u)) + (2 : ℂ) • u

theorem coe_Lr (i j : Fin 3) (φ : WhittakerBlock.smoothFunctions3) :
    ((Lr i j φ : WhittakerBlock.smoothFunctions3) : G3 → ℂ) =
      WhittakerBlock.archDeriv i j (φ : G3 → ℂ) - WhittakerBlock.archDeriv j i (φ : G3 → ℂ) := by
  rw [Lr_apply]; rfl

theorem coe_OmE (φ : WhittakerBlock.smoothFunctions3) :
    ((OmE φ : WhittakerBlock.smoothFunctions3) : G3 → ℂ) = OmFun (φ : G3 → ℂ) := by
  simp only [OmE, Om, OmFun, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, Module.End.mul_apply,
    Submodule.coe_add, Submodule.coe_smul, coe_Lr]

theorem OmE_Rsm (k : G3) (hk : archComponent3 (𝓞 ℚ) ℚ k ∈ orth3) (φ : WhittakerBlock.smoothFunctions3) :
    OmE (Rsm k φ) = Rsm k (OmE φ) := by
  simp only [OmE, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, Om_Rsm k hk, map_add, map_smul]

theorem Lr_eq_zero_of_mem_orthSpan {f : G3 → ℂ} (hfs : WhittakerBlock.IsArchSmooth3 f)
    (hf0 : ∀ i j : Fin 3, WhittakerBlock.archDeriv i j f - WhittakerBlock.archDeriv j i f = 0)
    (i j : Fin 3) (φ : WhittakerBlock.smoothFunctions3) (hφ : (φ : G3 → ℂ) ∈ WhittakerBlock.orthSpan f) :
    Lr i j φ = 0 := by
  set fφ : WhittakerBlock.smoothFunctions3 := ⟨f, hfs⟩ with hfφ
  have hL0 : ∀ a b : Fin 3, Lr a b fφ = 0 := fun a b => Subtype.ext (by rw [coe_Lr]; exact hf0 a b)
  let Z : Submodule ℂ (G3 → ℂ) := (LinearMap.ker (Lr i j)).map WhittakerBlock.smoothFunctions3.subtype
  have hle : WhittakerBlock.orthSpan f ≤ Z := by
    refine Submodule.span_le.mpr ?_
    rintro u ⟨k, hk1, hk2, rfl⟩
    refine ⟨Rsm k fφ, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, Lr_Rsm k hk2]
    simp [hL0]
  obtain ⟨ψ, hψ, hψφ⟩ := hle hφ
  have : ψ = φ := Subtype.ext hψφ
  rw [← this]; exact hψ

theorem OmE_eq_zero_of_mem_orthSpan {f : G3 → ℂ} (hfs : WhittakerBlock.IsArchSmooth3 f)
    (hf1 : OmFun f = 0)
    (φ : WhittakerBlock.smoothFunctions3) (hφ : (φ : G3 → ℂ) ∈ WhittakerBlock.orthSpan f) :
    OmE φ = 0 := by
  set fφ : WhittakerBlock.smoothFunctions3 := ⟨f, hfs⟩ with hfφ
  have hO0 : OmE fφ = 0 := Subtype.ext (by rw [coe_OmE]; exact hf1)
  let Z : Submodule ℂ (G3 → ℂ) := (LinearMap.ker OmE).map WhittakerBlock.smoothFunctions3.subtype
  have hle : WhittakerBlock.orthSpan f ≤ Z := by
    refine Submodule.span_le.mpr ?_
    rintro u ⟨k, hk1, hk2, rfl⟩
    refine ⟨Rsm k fφ, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, OmE_Rsm k hk2, hO0, map_zero]
  obtain ⟨ψ, hψ, hψφ⟩ := hle hφ
  have : ψ = φ := Subtype.ext hψφ
  rw [← this]; exact hψ

def Hull (f : G3 → ℂ) : Submodule ℂ (G3 → ℂ) where
  carrier := {u | ∀ k : G3, IsK k → ∃ φ ∈ WhittakerBlock.gKSpan f, (φ : G3 → ℂ) = Rf k u}
  zero_mem' := fun k hk => ⟨0, Submodule.zero_mem _, by rw [map_zero]; rfl⟩
  add_mem' := by
    intro u v hu hv k hk
    obtain ⟨φ, hφ, hφu⟩ := hu k hk
    obtain ⟨ψ, hψ, hψv⟩ := hv k hk
    exact ⟨φ + ψ, Submodule.add_mem _ hφ hψ, by rw [Submodule.coe_add, hφu, hψv, map_add]⟩
  smul_mem' := by
    intro c u hu k hk
    obtain ⟨φ, hφ, hφu⟩ := hu k hk
    exact ⟨c • φ, smul_mem_gKSpan hφ c, by rw [Submodule.coe_smul, hφu, map_smul]⟩

theorem mem_Hull {f : G3 → ℂ} {u : G3 → ℂ} :
    u ∈ Hull f ↔ ∀ k : G3, IsK k → ∃ φ ∈ WhittakerBlock.gKSpan f, (φ : G3 → ℂ) = Rf k u := Iff.rfl

theorem self_mem_Hull {f : G3 → ℂ} (hfs : WhittakerBlock.IsArchSmooth3 f) : f ∈ Hull f := by
  intro k hk
  refine ⟨Rsm k ⟨f, hfs⟩, Submodule.subset_span ?_, rfl⟩
  show Rf k f ∈ WhittakerBlock.orthSpan f
  exact translate_mem_orthSpan f hk

theorem Hull_le {f : G3 → ℂ} {M : Submodule ℂ (G3 → ℂ)} (hf : f ∈ M)
    (h4 : ∀ w ∈ M, ∀ k : G3, IsK k → Rf k w ∈ M)
    (h5 : ∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M) : Hull f ≤ M := by
  intro u hu
  obtain ⟨φ, hφ, hφu⟩ := hu 1 isK_one
  rw [Rf_one] at hφu
  rw [← hφu]
  exact coe_mem_of_mem_gKSpan hf h4 h5 hφ

theorem Hull_translate {f : G3 → ℂ} {u : G3 → ℂ} (hu : u ∈ Hull f) {k₀ : G3} (hk₀ : IsK k₀) :
    Rf k₀ u ∈ Hull f := by
  intro k hk
  obtain ⟨φ, hφ, hφu⟩ := hu (k * k₀) (isK_mul hk hk₀)
  exact ⟨φ, hφ, by rw [hφu, Rf_mul]⟩

theorem Hull_archDeriv {f : G3 → ℂ} {u : G3 → ℂ} (hu : u ∈ Hull f) (i j : Fin 3) :
    WhittakerBlock.archDeriv i j u ∈ Hull f := by
  intro k hk
  obtain ⟨φ₁, hφ₁, hφ₁u⟩ := hu 1 isK_one
  obtain ⟨φk, hφk, hφku⟩ := hu k hk
  rw [Rf_one] at hφ₁u
  have hR : Rsm k φ₁ = φk := Subtype.ext (by rw [coe_Rsm', hφ₁u, hφku])
  refine ⟨∑ i' : Fin 3, ∑ j' : Fin 3, ((RM k i' i * RM k j' j : ℝ) : ℂ) • WhittakerBlock.archDerivₗ i' j' φk, ?_, ?_⟩
  · exact Submodule.sum_mem _ (fun i' _ => Submodule.sum_mem _ (fun j' _ =>
      smul_mem_gKSpan (archDerivₗ_mem_gKSpan hφk i' j') _))
  · rw [← hR, ← Rsm_archDerivₗ k hk.2 i j φ₁, coe_Rsm', WhittakerBlock.coe_archDerivₗ_apply, hφ₁u]

theorem main (M : Submodule ℂ (G3 → ℂ))
    (hsm : ∀ w ∈ M, WhittakerBlock.IsArchSmooth3 w)
    (h3 : ∀ w ∈ M, WhittakerBlock.IsOrthFinite w)
    (h4 : ∀ w ∈ M, ∀ k : G3, IsK k → Rf k w ∈ M)
    (h5 : ∀ w ∈ M, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ M)
    (B : (G3 → ℂ) → (G3 → ℂ) → ℂ)
    (hBsymm : ∀ w ∈ M, ∀ w' ∈ M, B w' w = (starRingEnd ℂ) (B w w'))
    (hBlin : ∀ (z : ℂ), ∀ w₁ ∈ M, ∀ w₂ ∈ M, ∀ w' ∈ M, B (z • w₁ + w₂) w' = z * B w₁ w' + B w₂ w')
    (hBpos : ∀ w ∈ M, w ≠ 0 → 0 < (B w w).re)
    (hBskew : ∀ w ∈ M, ∀ w' ∈ M, ∀ i j : Fin 3,
      B (WhittakerBlock.archDeriv i j w) w' = - B w (WhittakerBlock.archDeriv i j w'))
    (h11 : ∃ (N₁ N₂ N₃ : ℕ) (a₁ : Fin (N₁ + 1) → ℂ) (a₂ : Fin (N₂ + 1) → ℂ) (a₃ : Fin (N₃ + 1) → ℂ),
        a₁ (Fin.last N₁) = 1 ∧ a₂ (Fin.last N₂) = 1 ∧ a₃ (Fin.last N₃) = 1 ∧
        ∀ w ∈ M,
          (∑ l, a₁ l • (WhittakerBlock.casimir1^[l] w)) = 0 ∧
          (∑ l, a₂ l • (WhittakerBlock.casimir2^[l] w)) = 0 ∧
          (∑ l, a₃ l • (WhittakerBlock.casimir3^[l] w)) = 0)
    (ℓ : ℕ) (f : G3 → ℂ) (hf : f ∈ M)
    (hfτ : (ℓ = 0 ∧ ∀ i j : Fin 3, WhittakerBlock.archDeriv i j f - WhittakerBlock.archDeriv j i f = 0) ∨
           (ℓ = 1 ∧ OmFun f = 0))
    (H : Submodule ℂ (G3 → ℂ))
    (hHmin : ∀ H' : Submodule ℂ (G3 → ℂ), H' ≤ M → f ∈ H' →
      (∀ w ∈ H', ∀ k : G3, IsK k → Rf k w ∈ H') →
      (∀ w ∈ H', ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ H') → H ≤ H') :
    ∃ E : Submodule ℂ (G3 → ℂ), FiniteDimensional ℂ ↥E ∧
      ∀ u ∈ H, ((ℓ = 0 ∧ ∀ i j : Fin 3, WhittakerBlock.archDeriv i j u - WhittakerBlock.archDeriv j i u = 0) ∨
           (ℓ = 1 ∧ OmFun u = 0)) → u ∈ E := by
  have hfin : WhittakerBlock.IsOrthFinite f := h3 f hf
  have hfs : WhittakerBlock.IsArchSmooth3 f := hsm f hf
  have hOle : WhittakerBlock.orthSpan f ≤ M := orthSpan_le hf h4
  have hcentre : ∀ φ ∈ WhittakerBlock.orthSpan f, WhittakerBlock.IsCentreFinite φ :=
    fun φ hφ => isCentreFinite_of_mem h11 (hOle hφ)
  have hgM : ∀ {x : WhittakerBlock.smoothFunctions3}, x ∈ WhittakerBlock.gKSpan f → (x : G3 → ℂ) ∈ M :=
    fun hx => coe_mem_of_mem_gKSpan hf h4 h5 hx

  let B' : WhittakerBlock.smoothFunctions3 → WhittakerBlock.smoothFunctions3 → ℂ := fun x y => B x y
  have hlin' : ∀ (z : ℂ), ∀ w₁ ∈ WhittakerBlock.gKSpan f, ∀ w₂ ∈ WhittakerBlock.gKSpan f,
      ∀ w' ∈ WhittakerBlock.gKSpan f, B' (z • w₁ + w₂) w' = z * B' w₁ w' + B' w₂ w' :=
    fun z w₁ h₁ w₂ h₂ w' h' => hBlin z _ (hgM h₁) _ (hgM h₂) _ (hgM h')
  have hsymm' : ∀ w ∈ WhittakerBlock.gKSpan f, ∀ w' ∈ WhittakerBlock.gKSpan f,
      B' w' w = (starRingEnd ℂ) (B' w w') := fun w h w' h' => hBsymm _ (hgM h) _ (hgM h')
  have hpos' : ∀ w ∈ WhittakerBlock.gKSpan f, w ≠ 0 → 0 < (B' w w).re :=
    fun w h hw => hBpos _ (hgM h) (fun h0 => hw (Subtype.ext h0))
  have hBsub1 : ∀ u₁ ∈ M, ∀ u₂ ∈ M, ∀ w ∈ M, B (u₁ - u₂) w = B u₁ w - B u₂ w := by
    intro u₁ h₁ u₂ h₂ w hw
    have := hBlin (-1) u₂ h₂ u₁ h₁ w hw
    rw [show u₁ - u₂ = (-1 : ℂ) • u₂ + u₁ by rw [neg_one_smul, neg_add_eq_sub], this]
    ring
  have hBsub2 : ∀ u ∈ M, ∀ v₁ ∈ M, ∀ v₂ ∈ M, B u (v₁ - v₂) = B u v₁ - B u v₂ := by
    intro u hu v₁ h₁ v₂ h₂
    rw [hBsymm _ (M.sub_mem h₁ h₂) _ hu, hBsub1 _ h₁ _ h₂ _ hu, map_sub, ← hBsymm _ h₁ _ hu, ← hBsymm _ h₂ _ hu]
  have hskew' : ∀ i j : Fin 3, ∀ x ∈ WhittakerBlock.gKSpan f, ∀ y ∈ WhittakerBlock.gKSpan f,
      B' (WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) x) y =
        -B' x (WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) y) := by
    intro i j x hx y hy
    show B ((Lr i j x : WhittakerBlock.smoothFunctions3) : G3 → ℂ) y = -B x ((Lr i j y : WhittakerBlock.smoothFunctions3) : G3 → ℂ)
    rw [coe_Lr, coe_Lr, hBsub1 _ (h5 _ (hgM hx) i j) _ (h5 _ (hgM hx) j i) _ (hgM hy),
      hBsub2 _ (hgM hx) _ (h5 _ (hgM hy) i j) _ (h5 _ (hgM hy) j i),
      hBskew _ (hgM hx) _ (hgM hy) i j, hBskew _ (hgM hx) _ (hgM hy) j i]
    ring

  have hH : H ≤ Hull f := hHmin (Hull f) (Hull_le hf h4 h5) (self_mem_Hull hfs)
    (fun w hw k hk => Hull_translate hw hk) (fun w hw i j => Hull_archDeriv hw i j)
  rcases hfτ with ⟨hℓ, hf0⟩ | ⟨hℓ, hf1⟩
  ·
    have hrot : ∀ i j : Fin 3, ∀ φ : WhittakerBlock.smoothFunctions3,
        (φ : G3 → ℂ) ∈ WhittakerBlock.orthSpan f →
          WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) φ = 0 :=
      fun i j φ hφ => Lr_eq_zero_of_mem_orthSpan hfs hf0 i j φ hφ
    have hFD := LanglandsTunnell.CubicInduction.finiteDimensional_invariants_gKSpan_of_isCentreFinite
      f hfin hcentre hrot B' hlin' hsymm' hpos' hskew'
    set F0 := (WhittakerBlock.gKSpan f).restrictScalars ℂ ⊓
      ⨅ i : Fin 3, ⨅ j : Fin 3,
        LinearMap.ker (WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1)) with hF0
    haveI : FiniteDimensional ℂ ↥F0 := hFD
    refine ⟨F0.map WhittakerBlock.smoothFunctions3.subtype, inferInstance, ?_⟩
    intro u hu hτ
    rcases hτ with ⟨-, hu0⟩ | ⟨hℓ1, -⟩
    · obtain ⟨φ, hφ, hφu⟩ := hH hu 1 isK_one
      rw [Rf_one] at hφu
      refine Submodule.mem_map.mpr ⟨φ, Submodule.mem_inf.mpr ⟨hφ, ?_⟩, hφu⟩
      simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro i j
      exact Subtype.ext (by rw [show WhittakerBlock.derivAction3 _ φ = Lr i j φ from rfl, coe_Lr, hφu,
        Submodule.coe_zero]; exact hu0 i j)
    · omega
  ·
    have hrot' : ∀ φ : WhittakerBlock.smoothFunctions3,
        (φ : G3 → ℂ) ∈ WhittakerBlock.orthSpan f → OmE φ = 0 :=
      fun φ hφ => OmE_eq_zero_of_mem_orthSpan hfs hf1 φ hφ
    have hK : ∀ i j : Fin 3, ∀ φ : WhittakerBlock.smoothFunctions3,
        (φ : G3 → ℂ) ∈ WhittakerBlock.orthSpan f →
          ((WhittakerBlock.derivAction3 (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) φ :
            WhittakerBlock.smoothFunctions3) : G3 → ℂ) ∈ WhittakerBlock.orthSpan f :=
      fun i j φ hφ => Lr_coe_mem_orthSpan f hfin i j φ hφ
    have hFD := LanglandsTunnell.CubicInduction.finiteDimensional_ker_rotationCasimir_add_two_gKSpan_of_isCentreFinite
      f hfin hcentre hrot' hK B' hlin' hsymm' hpos' hskew'
    set F1 := (WhittakerBlock.gKSpan f).restrictScalars ℂ ⊓ LinearMap.ker OmE with hF1
    haveI : FiniteDimensional ℂ ↥F1 := hFD
    refine ⟨F1.map WhittakerBlock.smoothFunctions3.subtype, inferInstance, ?_⟩
    intro u hu hτ
    rcases hτ with ⟨hℓ0, -⟩ | ⟨-, hu1⟩
    · omega
    · obtain ⟨φ, hφ, hφu⟩ := hH hu 1 isK_one
      rw [Rf_one] at hφu
      refine Submodule.mem_map.mpr ⟨φ, Submodule.mem_inf.mpr ⟨hφ, ?_⟩, hφu⟩
      rw [LinearMap.mem_ker]
      exact Subtype.ext (by rw [coe_OmE, hφu, Submodule.coe_zero]; exact hu1)

end WsF.CA

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
    (a : ℕ) (ha : a = 0 ∨ a = 1) (ℓ : ℕ) (hℓ : ℓ = 0 ∨ ℓ = 1)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hf : f ∈ M)
    (hfτ : ((ℓ = 0 ∧ ∀ i j : Fin 3, WhittakerBlock.archDeriv i j f - WhittakerBlock.archDeriv j i f = 0) ∨
           (ℓ = 1 ∧ (WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 0 1 f - WhittakerBlock.archDeriv 1 0 f) - WhittakerBlock.archDeriv 1 0 (WhittakerBlock.archDeriv 0 1 f - WhittakerBlock.archDeriv 1 0 f)) +
            (WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 0 2 f - WhittakerBlock.archDeriv 2 0 f) - WhittakerBlock.archDeriv 2 0 (WhittakerBlock.archDeriv 0 2 f - WhittakerBlock.archDeriv 2 0 f)) +
            (WhittakerBlock.archDeriv 1 2 (WhittakerBlock.archDeriv 1 2 f - WhittakerBlock.archDeriv 2 1 f) - WhittakerBlock.archDeriv 2 1 (WhittakerBlock.archDeriv 1 2 f - WhittakerBlock.archDeriv 2 1 f)) + (2 : ℂ) • f = 0)))
    (H : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)) (hHM : H ≤ M) (hfH : f ∈ H)
    (hHK : (∀ w ∈ H, ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ H))
    (hHD : (∀ w ∈ H, ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ H))
    (hHmin : ∀ H' : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), H' ≤ M → f ∈ H' →
      (∀ w ∈ H', ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
          (fun g => w (g * k)) ∈ H') →
      (∀ w ∈ H', ∀ i j : Fin 3, WhittakerBlock.archDeriv i j w ∈ H') → H ≤ H') :
    ∃ E : Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), FiniteDimensional ℂ ↥E ∧
      ∀ u ∈ H, ((ℓ = 0 ∧ ∀ i j : Fin 3, WhittakerBlock.archDeriv i j u - WhittakerBlock.archDeriv j i u = 0) ∨
           (ℓ = 1 ∧ (WhittakerBlock.archDeriv 0 1 (WhittakerBlock.archDeriv 0 1 u - WhittakerBlock.archDeriv 1 0 u) - WhittakerBlock.archDeriv 1 0 (WhittakerBlock.archDeriv 0 1 u - WhittakerBlock.archDeriv 1 0 u)) +
            (WhittakerBlock.archDeriv 0 2 (WhittakerBlock.archDeriv 0 2 u - WhittakerBlock.archDeriv 2 0 u) - WhittakerBlock.archDeriv 2 0 (WhittakerBlock.archDeriv 0 2 u - WhittakerBlock.archDeriv 2 0 u)) +
            (WhittakerBlock.archDeriv 1 2 (WhittakerBlock.archDeriv 1 2 u - WhittakerBlock.archDeriv 2 1 u) - WhittakerBlock.archDeriv 2 1 (WhittakerBlock.archDeriv 1 2 u - WhittakerBlock.archDeriv 2 1 u)) + (2 : ℂ) • u = 0)) → u ∈ E := by
  obtain ⟨B, hBsymm, hBlin, hBpos, hBskew, -⟩ := h10
  exact WsF.CA.main M (fun w hw => (h1 w hw).1) h3 (fun w hw k hk => h4 w hw k hk.1 hk.2) h5 B hBsymm hBlin
    hBpos hBskew h11 ℓ f hf hfτ H
    (fun H' hH'M hfH' hK hD => hHmin H' hH'M hfH' (fun w hw k hk1 hk2 => hK w hw k ⟨hk1, hk2⟩) hD)

end S_LanglandsTunnell_CubicInduction_exists_finiteDimensional_forall_mem_hull_of_rotationType_of_smoothingSubmodule
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_finiteDimensional_forall_mem_hull_of_rotationType_of_smoothingSubmodule (solution)
