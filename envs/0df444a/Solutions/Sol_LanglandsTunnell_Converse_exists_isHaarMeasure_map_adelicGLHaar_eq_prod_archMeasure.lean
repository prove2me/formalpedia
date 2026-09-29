-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_isHaarMeasure_map_adelicGLHaar_eq_prod_archMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/55dfb58b-92fc-512d-908e-4e146adda8c3

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_M4aHerbrand_AdeleTopologyFacts
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_LanglandsTunnell_Converse_isHaarMeasure_and_isMulRightInvariant_archMeasure
import Theorems.Thm_MeasureTheory_Measure_exists_isHaarMeasure_map_continuousMulEquiv_eq_prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_adelicGLHaar_eq_prod_archMeasure

set_option autoImplicit false

open NumberField AutomorphicForm MeasureTheory IsDedekindDomain
open NumberField.AdelicLevel LanglandsTunnell RSCarrier

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace HaarSplitProof

private theorem isReal_default : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal default

section SectionLaws

private theorem archRealGLAt_ratArchGL2_mul_finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    archRealGLAt isReal_default (ratArchGL2 g) * (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) = g :=
  mul_inv_cancel_left _ _

private theorem glArch_finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) : glArch (𝓞 ℚ) ℚ (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 :=
  (mem_finiteAdelicGL2Subgroup_iff ℚ _).mp (finFactor g).2

private theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) : glFin (𝓞 ℚ) ℚ (archRealGLAt isReal_default m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

private theorem glFin_finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    glFin (𝓞 ℚ) ℚ (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) = glFin (𝓞 ℚ) ℚ g := by
  show glFin (𝓞 ℚ) ℚ ((archRealGLAt isReal_default (ratArchGL2 g))⁻¹ * g) = _
  rw [map_mul, map_inv, glFin_archRealGLAt, inv_one, one_mul]

end SectionLaws

section RealComponent

private theorem ratArchGL2_mul (g g' : AdelicGL2 (𝓞 ℚ) ℚ) : ratArchGL2 (g * g') = ratArchGL2 g * ratArchGL2 g' := by
  unfold ratArchGL2
  simp only [map_mul]

private theorem ratArchGL2_one : ratArchGL2 1 = 1 := by
  unfold ratArchGL2
  simp only [map_one]

private theorem ratArchGL2_eq_archRealProjAt (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ratArchGL2 g = archRealProjAt isReal_default g :=
  Units.ext (Matrix.ext fun _ _ => rfl)

private theorem ratArchGL2_archRealGLAt (m : GL (Fin 2) ℝ) : ratArchGL2 (archRealGLAt isReal_default m) = m := by
  rw [ratArchGL2_eq_archRealProjAt]
  exact archRealProjAt_archRealGLAt _ m

private theorem ratArchGL2_finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) : ratArchGL2 (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
  unfold ratArchGL2
  rw [glArch_finFactor, map_one, map_one]

end RealComponent

section HomLaws

private theorem finFactor_coe (k : finiteAdelicGL2Subgroup ℚ) : finFactor (k : AdelicGL2 (𝓞 ℚ) ℚ) = k := by
  apply Subtype.ext
  show (archRealGLAt isReal_default (ratArchGL2 (k : AdelicGL2 (𝓞 ℚ) ℚ)))⁻¹ * (k : AdelicGL2 (𝓞 ℚ) ℚ) = k
  have hk : ratArchGL2 (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    unfold ratArchGL2
    rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).mp k.2, map_one, map_one]
  rw [hk, map_one, inv_one, one_mul]

private theorem finFactor_one : finFactor 1 = 1 := by
  apply Subtype.ext
  show (archRealGLAt isReal_default (ratArchGL2 1))⁻¹ * 1 = 1
  rw [ratArchGL2_one, map_one, inv_one, mul_one]

private theorem finFactor_mul (g g' : AdelicGL2 (𝓞 ℚ) ℚ) : finFactor (g * g') = finFactor g * finFactor g' := by
  apply Subtype.ext
  have hcomm := archRealGLAt_mul_comm_of_glArch_eq_one isReal_default (ratArchGL2 g')⁻¹ (glArch_finFactor g)
  rw [map_inv] at hcomm
  show (archRealGLAt isReal_default (ratArchGL2 (g * g')))⁻¹ * (g * g') =
    (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) * (finFactor g' : AdelicGL2 (𝓞 ℚ) ℚ)
  rw [ratArchGL2_mul, map_mul, mul_inv_rev]
  calc (archRealGLAt isReal_default (ratArchGL2 g'))⁻¹ * (archRealGLAt isReal_default (ratArchGL2 g))⁻¹ * (g * g')
      = (archRealGLAt isReal_default (ratArchGL2 g'))⁻¹ * (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) * g' := by
        show _ = _ * ((archRealGLAt isReal_default (ratArchGL2 g))⁻¹ * g) * g'
        simp only [mul_assoc]
    _ = (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) * (archRealGLAt isReal_default (ratArchGL2 g'))⁻¹ * g' := by
        rw [hcomm]
    _ = (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) * (finFactor g' : AdelicGL2 (𝓞 ℚ) ℚ) := by
        show _ = _ * ((archRealGLAt isReal_default (ratArchGL2 g'))⁻¹ * g')
        rw [mul_assoc]

end HomLaws

section ComponentIso

open NumberField.InfinitePlace.Completion

private theorem continuous_generalLinearGroup_map {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f))

private theorem continuous_ringEquivRealOfIsReal : Continuous (ringEquivRealOfIsReal isReal_default) := by
  have h : (fun x => ringEquivRealOfIsReal isReal_default x) = isometryEquivRealOfIsReal isReal_default := rfl
  show Continuous fun x => ringEquivRealOfIsReal isReal_default x
  rw [h]
  exact (isometryEquivRealOfIsReal isReal_default).continuous

private theorem continuous_ringEquivRealOfIsReal_symm : Continuous (ringEquivRealOfIsReal isReal_default).symm := by
  have h : (fun r => (ringEquivRealOfIsReal isReal_default).symm r)
      = (isometryEquivRealOfIsReal isReal_default).symm := rfl
  show Continuous fun r => (ringEquivRealOfIsReal isReal_default).symm r
  rw [h]
  exact (isometryEquivRealOfIsReal isReal_default).symm.continuous

private theorem continuous_ratArchGL2 : Continuous ratArchGL2 := by
  unfold ratArchGL2
  exact (continuous_generalLinearGroup_map _ continuous_ringEquivRealOfIsReal).comp
    ((continuous_archComponent ℚ default).comp (continuous_glArch (𝓞 ℚ) ℚ))

private theorem continuous_glEquivOfRingEquiv {A B : Type*} [NormedField A] [NormedField B] (e : A ≃+* B)
    (he : Continuous e) : Continuous (glEquivOfRingEquiv e) := by
  unfold glEquivOfRingEquiv
  exact Continuous.units_map (RingEquiv.mapMatrix (m := Fin 2) e).toMulEquiv.toMonoidHom
    ((continuous_id.matrix_map he : Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map e))

private theorem continuous_archMatrixUpdate (w : InfinitePlace ℚ) : Continuous (archMatrixUpdate ℚ w) := by
  refine continuous_matrix fun i j => continuous_pi fun w' => ?_
  show Continuous fun m : Matrix (Fin 2) (Fin 2) w.Completion => archMatrixPiEquiv ℚ (archMatrixUpdate ℚ w m) w' i j
  simp_rw [archMatrixPiEquiv_archMatrixUpdate]
  obtain rfl : w' = w := Subsingleton.elim w' w
  simp only [Function.update_self]
  exact continuous_id.matrix_elem i j

private theorem continuous_archGLIncl (w : InfinitePlace ℚ) : Continuous (archGLIncl ℚ w) := by
  unfold archGLIncl
  exact Continuous.units_map _ (continuous_archMatrixUpdate w)

private theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl ℚ) := by
  have h₁ : Continuous fun p : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ) ×
      Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) => (adelicMatrixProdEquiv ℚ).symm p :=
    continuous_matrix fun i j => (continuous_fst.matrix_elem i j).prodMk (continuous_snd.matrix_elem i j)
  have h₂ : Continuous (Units.mapEquiv (adelicMatrixProdEquiv ℚ).symm.toMulEquiv) :=
    Continuous.units_map (adelicMatrixProdEquiv ℚ).symm.toMulEquiv.toMonoidHom h₁
  have h₃ : Continuous (MulEquiv.prodUnits.symm : GL (Fin 2) (InfiniteAdeleRing ℚ) ×
      GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) → _) :=
    (Homeomorph.prodUnits (α := Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ))
      (β := Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))).symm.continuous
  unfold adelicArchGLIncl
  exact h₂.comp (h₃.comp (continuous_id.prodMk continuous_const))

private theorem continuous_archRealGLAt : Continuous (archRealGLAt (F := ℚ) isReal_default) :=
  continuous_adelicArchGLIncl.comp ((continuous_archGLIncl default).comp
    (continuous_glEquivOfRingEquiv _ continuous_ringEquivRealOfIsReal_symm))

private theorem continuous_coe_finFactor : Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) :=
  ((continuous_archRealGLAt.comp continuous_ratArchGL2).inv).mul continuous_id

private theorem continuous_finFactor : Continuous finFactor :=
  continuous_coe_finFactor.subtype_mk fun g => (finFactor g).2

private theorem ratArchGL2_coe (k : finiteAdelicGL2Subgroup ℚ) : ratArchGL2 (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
  unfold ratArchGL2
  rw [(mem_finiteAdelicGL2Subgroup_iff ℚ _).mp k.2, map_one, map_one]

private theorem finFactor_archRealGLAt (m : GL (Fin 2) ℝ) : finFactor (archRealGLAt isReal_default m) = 1 := by
  apply Subtype.ext
  show (archRealGLAt isReal_default (ratArchGL2 (archRealGLAt isReal_default m)))⁻¹ *
    archRealGLAt isReal_default m = 1
  rw [ratArchGL2_archRealGLAt, inv_mul_cancel]

private noncomputable def componentIso : AdelicGL2 (𝓞 ℚ) ℚ ≃ₜ* GL (Fin 2) ℝ × finiteAdelicGL2Subgroup ℚ where
  toFun g := (ratArchGL2 g, finFactor g)
  invFun p := archRealGLAt isReal_default p.1 * (p.2 : AdelicGL2 (𝓞 ℚ) ℚ)
  left_inv g := archRealGLAt_ratArchGL2_mul_finFactor g
  right_inv p := by
    obtain ⟨m, k⟩ := p
    refine Prod.ext ?_ ?_
    · show ratArchGL2 (archRealGLAt isReal_default m * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = m
      rw [ratArchGL2_mul, ratArchGL2_archRealGLAt, ratArchGL2_coe, mul_one]
    · show finFactor (archRealGLAt isReal_default m * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = k
      rw [finFactor_mul, finFactor_archRealGLAt, finFactor_coe, one_mul]
  map_mul' g g' := Prod.ext (ratArchGL2_mul g g') (finFactor_mul g g')
  continuous_toFun := continuous_ratArchGL2.prodMk continuous_finFactor
  continuous_invFun :=
    (continuous_archRealGLAt.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)

private theorem componentIso_apply (g : AdelicGL2 (𝓞 ℚ) ℚ) : componentIso g = (ratArchGL2 g, finFactor g) := rfl

end ComponentIso

section Generic

private theorem sigmaCompactSpace_mulOpposite {M : Type*} [TopologicalSpace M] [SigmaCompactSpace M] :
    SigmaCompactSpace Mᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.isClosedEmbedding.sigmaCompactSpace

private theorem sigmaCompactSpace_units {M : Type*} [Monoid M] [TopologicalSpace M] [T1Space M] [ContinuousMul M]
    [SigmaCompactSpace M] : SigmaCompactSpace Mˣ :=
  haveI := sigmaCompactSpace_mulOpposite (M := M)
  Units.isClosedEmbedding_embedProduct.sigmaCompactSpace

private theorem sigmaCompactSpace_matrix {A : Type*} [TopologicalSpace A] [SigmaCompactSpace A] :
    SigmaCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
  inferInstanceAs (SigmaCompactSpace (Fin 2 → Fin 2 → A))

private theorem sigmaCompactSpace_generalLinearGroup {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] [SigmaCompactSpace A] : SigmaCompactSpace (GL (Fin 2) A) :=
  haveI := sigmaCompactSpace_matrix (A := A)
  sigmaCompactSpace_units

private theorem sigmaCompactSpace_of_isClosed {G : Type*} [Group G] [TopologicalSpace G] [SigmaCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : SigmaCompactSpace H :=
  hH.sigmaCompactSpace

private theorem sigmaFinite_of_isHaarMeasure {G : Type*} [Group G] [TopologicalSpace G] [SigmaCompactSpace G]
    [MeasurableSpace G] (μ : Measure G) [μ.IsHaarMeasure] : SigmaFinite μ :=
  inferInstance

end Generic

section Adelic

private scoped instance sigmaCompactSpace_gl_real : SigmaCompactSpace (GL (Fin 2) ℝ) :=
  sigmaCompactSpace_generalLinearGroup

private scoped instance sigmaCompactSpace_adelicGL2 : SigmaCompactSpace (AdelicGL2 (𝓞 ℚ) ℚ) :=
  sigmaCompactSpace_generalLinearGroup

private scoped instance sigmaCompactSpace_finiteAdelicGL2Subgroup : SigmaCompactSpace (finiteAdelicGL2Subgroup ℚ) :=
  sigmaCompactSpace_of_isClosed _ (isClosed_finiteAdelicGL2Subgroup ℚ)

private theorem sigmaFinite_adelicGLHaar : SigmaFinite (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  sigmaFinite_of_isHaarMeasure _

end Adelic

section Assembly

private scoped instance : MeasurableSpace (GL (Fin 2) ℝ) := borel (GL (Fin 2) ℝ)

private scoped instance : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩

private theorem locallyCompactSpace_gl_real : LocallyCompactSpace (GL (Fin 2) ℝ) :=
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  inferInstance

private theorem isHaarMeasure_archMeasure : archMeasure.IsHaarMeasure ∧ archMeasure.IsMulRightInvariant :=
  LanglandsTunnell.Converse.isHaarMeasure_and_isMulRightInvariant_archMeasure

private theorem exists_prod_split [archMeasure.IsHaarMeasure] :
    ∃ μf : Measure (finiteAdelicGL2Subgroup ℚ), μf.IsHaarMeasure ∧
      ((AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsMulRightInvariant → μf.IsMulRightInvariant) ∧
        (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).map componentIso = archMeasure.prod μf :=
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  haveI := locallyCompactSpace_gl_real
  MeasureTheory.Measure.exists_isHaarMeasure_map_continuousMulEquiv_eq_prod
    (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) archMeasure componentIso

private theorem haar_splits :
    ∃ μf : Measure (finiteAdelicGL2Subgroup ℚ), μf.IsHaarMeasure ∧ μf.IsMulRightInvariant ∧
      Measure.map (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (LanglandsTunnell.ratArchGL2 g, RSCarrier.finFactor g))
          (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) =
        RSCarrier.archMeasure.prod μf := by
  haveI := isHaarMeasure_archMeasure.1
  obtain ⟨μf, hHaar, hRight, hmap⟩ := exists_prod_split
  exact ⟨μf, hHaar, hRight (NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar ℚ), hmap⟩

end Assembly

end HaarSplitProof
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_adelicGLHaar_eq_prod_archMeasure.HaarSplitProof"

theorem solution :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel (GL (Fin 2) ℝ)
    ∃ μf : Measure (finiteAdelicGL2Subgroup ℚ), μf.IsHaarMeasure ∧ μf.IsMulRightInvariant ∧
      Measure.map (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (LanglandsTunnell.ratArchGL2 g, RSCarrier.finFactor g))
          (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) =
        RSCarrier.archMeasure.prod μf :=
  HaarSplitProof.haar_splits

end S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_adelicGLHaar_eq_prod_archMeasure
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_adelicGLHaar_eq_prod_archMeasure (solution)
