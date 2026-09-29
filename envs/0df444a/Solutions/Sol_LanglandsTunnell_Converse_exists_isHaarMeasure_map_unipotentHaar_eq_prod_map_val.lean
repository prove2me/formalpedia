-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/97968f5b-7594-564f-8b5e-c5148575817e

import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_M4aHerbrand_AdeleTopologyFacts
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_isHaarMeasure_and_isMulRightInvariant_unipotentHaar
import Theorems.Thm_MeasureTheory_Measure_exists_isHaarMeasure_map_continuousMulEquiv_eq_prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val

set_option autoImplicit false

open NumberField AutomorphicForm MeasureTheory

attribute [local instance] NumberField.AdelicHaar.glBorel

open NumberField.AdelicLevel LanglandsTunnell RSCarrier

namespace UnipotentHaarSplitting

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
    [IsTopologicalRing A]
    [T2Space A] [SigmaCompactSpace A] : SigmaCompactSpace (GL (Fin 2) A) :=
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

attribute [local instance] AdelicHaar.glBorel

private theorem sigmaFinite_adelicGLHaar : SigmaFinite (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) :=
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  sigmaFinite_of_isHaarMeasure _

end Adelic

end UnipotentHaarSplitting
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val.UnipotentHaarSplitting"

namespace UnipotentHaarSplitting

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val.UnipotentHaarSplitting"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val.UnipotentHaarSplitting"

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val.UnipotentHaarSplitting"

end UnipotentHaarSplitting
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val.UnipotentHaarSplitting"

namespace UnipotentHaarSplitting

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
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val.UnipotentHaarSplitting"

end UnipotentHaarSplitting
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val.UnipotentHaarSplitting"

namespace UnipotentHaarSplitting

section UnipotentIso

open NumberField.InfinitePlace.Completion

private theorem generalLinearGroup_map_unipotentGL2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x : A) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 x) = unipotentGL2 (f x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map]

private theorem unipotentGL2_mem_adelicUnipotent (x : AdeleRing (𝓞 ℚ) ℚ) : unipotentGL2 x ∈ adelicUnipotent ℚ :=
  ⟨Multiplicative.ofAdd x, rfl⟩

private theorem unipotentGL2_mem_realUnipotent (r : ℝ) : unipotentGL2 r ∈ realUnipotent :=
  ⟨Multiplicative.ofAdd r, rfl⟩

private theorem exists_eq_unipotentGL2_of_mem_adelicUnipotent {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : g ∈ adelicUnipotent ℚ) :
    ∃ x : AdeleRing (𝓞 ℚ) ℚ, g = unipotentGL2 x := by
  obtain ⟨x, rfl⟩ := hg
  exact ⟨x.toAdd, rfl⟩

private theorem exists_eq_unipotentGL2_of_mem_realUnipotent {m : GL (Fin 2) ℝ} (hm : m ∈ realUnipotent) :
    ∃ r : ℝ, m = unipotentGL2 r := by
  obtain ⟨r, rfl⟩ := hm
  exact ⟨r.toAdd, rfl⟩

private theorem ratArchGL2_unipotentGL2 (x : AdeleRing (𝓞 ℚ) ℚ) :
    ratArchGL2 (unipotentGL2 x) = unipotentGL2 (ringEquivRealOfIsReal isReal_default (x.1 default)) := by
  unfold LanglandsTunnell.ratArchGL2 AdelicLevel.archComponent AdelicLevel.glArch
  rw [generalLinearGroup_map_unipotentGL2, generalLinearGroup_map_unipotentGL2, generalLinearGroup_map_unipotentGL2]
  rfl

private theorem ratArchGL2_mem_realUnipotent {n : AdelicGL2 (𝓞 ℚ) ℚ} (hn : n ∈ adelicUnipotent ℚ) :
    ratArchGL2 n ∈ realUnipotent := by
  obtain ⟨x, rfl⟩ := exists_eq_unipotentGL2_of_mem_adelicUnipotent hn
  rw [ratArchGL2_unipotentGL2]
  exact unipotentGL2_mem_realUnipotent _

private theorem adelicGL2_ext {g h : AdelicGL2 (𝓞 ℚ) ℚ} (ha : glArch (𝓞 ℚ) ℚ g = glArch (𝓞 ℚ) ℚ h)
    (hf : glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ h) : g = h := by
  ext i j
  have h1 := congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing ℚ) => Units.val u i j) ha
  have h2 := congrArg (fun u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) => Units.val u i j) hf
  exact Prod.ext h1 h2

private theorem infiniteAdeleGL2_ext {a b : GL (Fin 2) (InfiniteAdeleRing ℚ)}
    (h : archComponent ℚ default a = archComponent ℚ default b) : a = b := by
  ext i j
  funext w
  obtain rfl : w = default := Subsingleton.elim w default
  exact congrArg (fun u : GL (Fin 2) (default : InfinitePlace ℚ).Completion => Units.val u i j) h

private theorem archComponent_glArch_archRealGLAt (m : GL (Fin 2) ℝ) :
    archComponent ℚ default (glArch (𝓞 ℚ) ℚ (archRealGLAt isReal_default m)) =
      Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal isReal_default).symm.toRingHom m := by
  have h := ratArchGL2_archRealGLAt m
  unfold LanglandsTunnell.ratArchGL2 at h
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have hij : ringEquivRealOfIsReal isReal_default
      (Units.val (archComponent ℚ default (glArch (𝓞 ℚ) ℚ (archRealGLAt isReal_default m))) i j) = Units.val m i j :=
    congrArg (fun u : GL (Fin 2) ℝ => Units.val u i j) h
  show Units.val (archComponent ℚ default (glArch (𝓞 ℚ) ℚ (archRealGLAt isReal_default m))) i j =
    (ringEquivRealOfIsReal isReal_default).symm (Units.val m i j)
  rw [← hij, RingEquiv.symm_apply_apply]

private theorem archRealGLAt_unipotentGL2_eq (r : ℝ) :
    archRealGLAt isReal_default (unipotentGL2 r) =
      unipotentGL2 (Units.val (archRealGLAt isReal_default (unipotentGL2 r)) 0 1) := by
  set x : AdeleRing (𝓞 ℚ) ℚ := Units.val (archRealGLAt isReal_default (unipotentGL2 r)) 0 1 with hx
  have hfin : glFin (𝓞 ℚ) ℚ (archRealGLAt isReal_default (unipotentGL2 r)) = 1 := glFin_archRealGLAt _
  have hx2 : x.2 = 0 := by
    have h01 : Units.val (glFin (𝓞 ℚ) ℚ (archRealGLAt isReal_default (unipotentGL2 r))) 0 1 =
        Units.val (1 : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) 0 1 :=
      congrArg (fun u : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) => Units.val u 0 1) hfin
    rw [glFin_apply] at h01
    rw [hx]
    rw [h01]
    simp
  have harch := archComponent_glArch_archRealGLAt (unipotentGL2 r)
  rw [generalLinearGroup_map_unipotentGL2] at harch
  have hx1 : x.1 default = (ringEquivRealOfIsReal isReal_default).symm r := by
    have h01 : Units.val
        (archComponent ℚ default (glArch (𝓞 ℚ) ℚ (archRealGLAt isReal_default (unipotentGL2 r)))) 0 1 =
        Units.val (unipotentGL2 ((ringEquivRealOfIsReal isReal_default).symm r)) 0 1 :=
      congrArg (fun u : GL (Fin 2) (default : InfinitePlace ℚ).Completion => Units.val u 0 1) harch
    rw [archComponent_apply, glArch_apply] at h01
    rw [hx]
    rw [h01]
    simp
  refine adelicGL2_ext (infiniteAdeleGL2_ext ?_) ?_
  · rw [harch]
    unfold AdelicLevel.glArch AdelicLevel.archComponent
    rw [generalLinearGroup_map_unipotentGL2, generalLinearGroup_map_unipotentGL2]
    exact congrArg unipotentGL2 hx1.symm
  · rw [hfin]
    unfold AdelicLevel.glFin
    rw [generalLinearGroup_map_unipotentGL2]
    change (1 : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) = unipotentGL2 x.2
    rw [hx2, unipotentGL2_zero]

private theorem archRealGLAt_mem_adelicUnipotent {m : GL (Fin 2) ℝ} (hm : m ∈ realUnipotent) :
    archRealGLAt isReal_default m ∈ adelicUnipotent ℚ := by
  obtain ⟨r, rfl⟩ := exists_eq_unipotentGL2_of_mem_realUnipotent hm
  rw [archRealGLAt_unipotentGL2_eq]
  exact unipotentGL2_mem_adelicUnipotent _

private theorem finFactor_mem_finUnipotent {n : AdelicGL2 (𝓞 ℚ) ℚ} (hn : n ∈ adelicUnipotent ℚ) :
    finFactor n ∈ finUnipotent := by
  show (finFactor n : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ
  exact (adelicUnipotent ℚ).mul_mem
    ((adelicUnipotent ℚ).inv_mem (archRealGLAt_mem_adelicUnipotent (ratArchGL2_mem_realUnipotent hn))) hn

private theorem archRealGLAt_mul_mem_adelicUnipotent {m : GL (Fin 2) ℝ} (hm : m ∈ realUnipotent)
    (k : finiteAdelicGL2Subgroup ℚ) (hk : k ∈ finUnipotent) :
    archRealGLAt isReal_default m * (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ adelicUnipotent ℚ :=
  (adelicUnipotent ℚ).mul_mem (archRealGLAt_mem_adelicUnipotent hm) hk

private noncomputable def unipotentComponentIso : adelicUnipotent ℚ ≃ₜ* realUnipotent × finUnipotent where
  toFun n := (⟨ratArchGL2 n, ratArchGL2_mem_realUnipotent n.2⟩, ⟨finFactor n, finFactor_mem_finUnipotent n.2⟩)
  invFun p := ⟨archRealGLAt isReal_default p.1 * (p.2 : finiteAdelicGL2Subgroup ℚ),
    archRealGLAt_mul_mem_adelicUnipotent p.1.2 _ p.2.2⟩
  left_inv n := Subtype.ext (archRealGLAt_ratArchGL2_mul_finFactor n)
  right_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext (Subtype.ext ?_))
    · show ratArchGL2 (archRealGLAt isReal_default p.1 * (p.2 : finiteAdelicGL2Subgroup ℚ)) = p.1
      rw [ratArchGL2_mul, ratArchGL2_archRealGLAt, ratArchGL2_coe, mul_one]
    · show ((finFactor (archRealGLAt isReal_default p.1 * (p.2 : finiteAdelicGL2Subgroup ℚ)) :
          finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = ((p.2 : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)
      rw [finFactor_mul, finFactor_archRealGLAt, finFactor_coe, one_mul]
  map_mul' n n' := Prod.ext (Subtype.ext (ratArchGL2_mul n n')) (Subtype.ext (finFactor_mul n n'))
  continuous_toFun :=
    ((continuous_ratArchGL2.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_finFactor.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    ((continuous_archRealGLAt.comp (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).subtype_mk _

private theorem unipotentComponentIso_apply (n : adelicUnipotent ℚ) :
    ((unipotentComponentIso n).1 : GL (Fin 2) ℝ) = ratArchGL2 n ∧
      (((unipotentComponentIso n).2 : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = finFactor n :=
  ⟨rfl, rfl⟩

end UnipotentIso
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val.UnipotentHaarSplitting"

end UnipotentHaarSplitting
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val.UnipotentHaarSplitting"

namespace UnipotentHaarSplitting

open Topology

section Legs
variable {R : Type*} [CommRing R] [TopologicalSpace R] [T2Space R]

omit [TopologicalSpace R] [T2Space R] in

private theorem coe_range_unipotentGL2Hom :
    ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) =
      {g : GL (Fin 2) R | Units.val g 0 0 = 1 ∧ Units.val g 1 0 = 0 ∧ Units.val g 1 1 = 1} := by
  ext g
  constructor
  · rintro ⟨y, rfl⟩
    change Units.val (unipotentGL2 y.toAdd) 0 0 = 1 ∧ Units.val (unipotentGL2 y.toAdd) 1 0 = 0 ∧
      Units.val (unipotentGL2 y.toAdd) 1 1 = 1
    simp [unipotentGL2]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd (Units.val g 0 1), ?_⟩
    change unipotentGL2 (Units.val g 0 1) = g
    refine Units.ext ?_
    rw [unipotentGL2_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

private theorem isClosed_range_unipotentGL2Hom :
    IsClosed ((unipotentGL2Hom (R := R)).range : Set (GL (Fin 2) R)) := by
  rw [coe_range_unipotentGL2Hom]
  have hc : Continuous fun g : GL (Fin 2) R => Units.val g := Units.continuous_val
  exact (isClosed_eq (hc.matrix_elem 0 0) continuous_const).inter
    ((isClosed_eq (hc.matrix_elem 1 0) continuous_const).inter
      (isClosed_eq (hc.matrix_elem 1 1) continuous_const))

private theorem locallyCompactSpace_of_isClosed {G : Type*} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : LocallyCompactSpace H :=
  hH.locallyCompactSpace

private theorem locallyCompactSpace_gl_real : LocallyCompactSpace (GL (Fin 2) ℝ) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : Matrix (Fin 2) (Fin 2) ℝ ≃ₜ
      (Matrix (Fin 2) (Fin 2) ℝ)ᵐᵒᵖ).symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

private theorem map_prodMap_prod {X₁ X₂ Y₁ Y₂ : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y₁]
    [MeasurableSpace Y₂] (μ₁ : Measure X₁) (μ₂ : Measure X₂) [SFinite μ₁] [SFinite μ₂] {f : X₁ → Y₁}
    {g : X₂ → Y₂} (hf : Measurable f) (hg : Measurable g) :
    (μ₁.prod μ₂).map (Prod.map f g) = (μ₁.map f).prod (μ₂.map g) :=
  (Measure.map_prod_map μ₁ μ₂ hf hg).symm

end Legs
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val.UnipotentHaarSplitting"

private theorem isClosed_subgroupOf {A : Type*} [Group A] [TopologicalSpace A] (H K : Subgroup A)
    (hH : IsClosed (H : Set A)) : IsClosed ((H.subgroupOf K : Subgroup K) : Set K) := by
  rw [Subgroup.coe_subgroupOf]
  exact hH.preimage continuous_subtype_val

private theorem map_components_eq_prod_map_val {G A₁ A₂ : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [Group A₁] [TopologicalSpace A₁] [MeasurableSpace A₁] [BorelSpace A₁] [Group A₂]
    [TopologicalSpace A₂] [MeasurableSpace A₂] [BorelSpace A₂] (H₁ : Subgroup A₁) (H₂ : Subgroup A₂)
    (e : G ≃ₜ* H₁ × H₂) (μ : Measure G) (μ₁ : Measure H₁) (μ₂ : Measure H₂) [SFinite μ₁] [SFinite μ₂]
    (hsplit : μ.map e = μ₁.prod μ₂) :
    μ.map (fun g => (((e g).1 : A₁), ((e g).2 : A₂))) = (μ₁.map Subtype.val).prod (μ₂.map Subtype.val) := by
  have hfun : (fun g : G => (((e g).1 : A₁), ((e g).2 : A₂))) = Prod.map Subtype.val Subtype.val ∘ e := by
    funext g
    rfl
  have he : Measurable e :=
    (continuous_fst.comp e.continuous).measurable.prodMk (continuous_snd.comp e.continuous).measurable
  rw [hfun, ← Measure.map_map (measurable_subtype_coe.prodMap measurable_subtype_coe) he, hsplit,
    Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe]

private theorem sfinite_of_isHaarMeasure {H : Type*} [Group H] [TopologicalSpace H] [SigmaCompactSpace H]
    [MeasurableSpace H] (ν : Measure H) [ν.IsHaarMeasure] : SFinite ν :=
  inferInstance

private theorem exists_isHaarMeasure {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H] : ∃ ν : Measure H, ν.IsHaarMeasure :=
  ⟨Measure.haar, inferInstance⟩

end UnipotentHaarSplitting
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val.UnipotentHaarSplitting"

namespace UnipotentHaarSplitting

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

private scoped instance : MeasurableSpace (GL (Fin 2) ℝ) := borel (GL (Fin 2) ℝ)

private scoped instance : BorelSpace (GL (Fin 2) ℝ) := ⟨rfl⟩

private scoped instance : LocallyCompactSpace (GL (Fin 2) ℝ) := locallyCompactSpace_gl_real

private theorem isClosed_realUnipotent : IsClosed ((realUnipotent : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) :=
  isClosed_range_unipotentGL2Hom

private theorem isClosed_finUnipotent :
    IsClosed ((finUnipotent : Subgroup (finiteAdelicGL2Subgroup ℚ)) : Set (finiteAdelicGL2Subgroup ℚ)) :=
  isClosed_subgroupOf _ _ isClosed_range_unipotentGL2Hom

private scoped instance : LocallyCompactSpace realUnipotent := locallyCompactSpace_of_isClosed _ isClosed_realUnipotent

private scoped instance : SigmaCompactSpace realUnipotent := sigmaCompactSpace_of_isClosed _ isClosed_realUnipotent

private scoped instance : SigmaCompactSpace finUnipotent := sigmaCompactSpace_of_isClosed _ isClosed_finUnipotent

private theorem isHaarMeasure_unipotentHaar :
    (unipotentHaar ℚ).IsHaarMeasure ∧ (unipotentHaar ℚ).IsMulRightInvariant :=
  AutomorphicForm.isHaarMeasure_and_isMulRightInvariant_unipotentHaar ℚ

private theorem exists_prod_split (μ₁ : Measure realUnipotent) [μ₁.IsHaarMeasure] [(unipotentHaar ℚ).IsHaarMeasure] :
    ∃ μ₂ : Measure finUnipotent, μ₂.IsHaarMeasure ∧
      ((unipotentHaar ℚ).IsMulRightInvariant → μ₂.IsMulRightInvariant) ∧
        (unipotentHaar ℚ).map unipotentComponentIso = μ₁.prod μ₂ :=
  MeasureTheory.Measure.exists_isHaarMeasure_map_continuousMulEquiv_eq_prod (unipotentHaar ℚ) μ₁
    unipotentComponentIso

private theorem unipotentHaar_splits :
    ∃ (μNArch : Measure RSCarrier.realUnipotent) (μNFin : Measure RSCarrier.finUnipotent),
      μNArch.IsHaarMeasure ∧ μNFin.IsHaarMeasure ∧
        Measure.map
            (fun n : adelicUnipotent ℚ => (LanglandsTunnell.ratArchGL2 n, RSCarrier.finFactor n))
            (unipotentHaar ℚ) =
          (Measure.map Subtype.val μNArch).prod (Measure.map Subtype.val μNFin) := by
  haveI hN : (unipotentHaar ℚ).IsHaarMeasure := isHaarMeasure_unipotentHaar.1
  obtain ⟨μ₁, hμ₁⟩ := exists_isHaarMeasure (H := realUnipotent)
  obtain ⟨μ₂, hμ₂, -, hsplit⟩ := exists_prod_split μ₁
  haveI := sfinite_of_isHaarMeasure μ₁
  haveI := sfinite_of_isHaarMeasure μ₂
  exact ⟨μ₁, μ₂, hμ₁, hμ₂,
    map_components_eq_prod_map_val realUnipotent finUnipotent unipotentComponentIso (unipotentHaar ℚ) μ₁ μ₂ hsplit⟩

end UnipotentHaarSplitting
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val.UnipotentHaarSplitting"

theorem solution :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel (GL (Fin 2) ℝ)
    ∃ (μNArch : Measure RSCarrier.realUnipotent) (μNFin : Measure RSCarrier.finUnipotent),
      μNArch.IsHaarMeasure ∧ μNFin.IsHaarMeasure ∧
        Measure.map
            (fun n : adelicUnipotent ℚ => (LanglandsTunnell.ratArchGL2 n, RSCarrier.finFactor n))
            (unipotentHaar ℚ) =
          (Measure.map Subtype.val μNArch).prod (Measure.map Subtype.val μNFin) :=
  UnipotentHaarSplitting.unipotentHaar_splits

end S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_isHaarMeasure_map_unipotentHaar_eq_prod_map_val (solution)
