-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.integrable_finCell_of_integrable_of_factorsAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2af7efdf-5528-5de6-91f6-6d4d27245ba5

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Theorems.Thm_HaarQuotient_map_mk_withDensity_eq_smul_measure
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_placeEmbed
import Theorems.Thm_MeasureTheory_Measure_exists_isHaarMeasure_map_continuousMulEquiv_eq_prod
import Theorems.Thm_HaarQuotient_lintegral_density_mul_eq_one
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_integrable_finCell_of_integrable_of_factorsAt
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory UnramifiedWhittaker AdelicDock
open NumberField.AdelicLevel Topology NumberField.TateGlobal LanglandsTunnell.TateLocal
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace KcFinCellTonelli

section Continuity

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

open scoped Classical in

theorem continuous_splice (a : FiniteAdeleRing R K) : Continuous (splice R K v a) := by
  let S : Set (HeightOneSpectrum R) := {w | w ≠ v ∧ a w ∈ w.adicCompletionIntegers K}
  have hS : (Filter.cofinite : Filter (HeightOneSpectrum R)) ≤ Filter.principal S := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite]
    refine (((Filter.eventually_cofinite.1 a.2)).union (Set.finite_singleton v)).subset fun w hw => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff, not_or, not_not] at h
    exact hw ⟨h.2, h.1⟩
  let f₀ : v.adicCompletion K →
      RestrictedProduct (fun w : HeightOneSpectrum R => w.adicCompletion K)
        (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) (Filter.principal S) :=
    fun t => ⟨Function.update (⇑a) v t, Filter.eventually_principal.2 fun w hw => by
      rw [Function.update_of_ne hw.1]
      exact hw.2⟩
  have hf₀ : Continuous f₀ :=
    RestrictedProduct.continuous_rng_of_principal.2 (continuous_const.update v continuous_id)
  have heq : splice R K v a = RestrictedProduct.inclusion _ _ hS ∘ f₀ := by
    funext t
    rfl
  rw [heq]
  exact (RestrictedProduct.continuous_inclusion hS).comp hf₀

theorem continuous_localMat : Continuous (localMat R K v) :=
  continuous_matrix fun i j => (continuous_splice R K v _).comp (continuous_id.matrix_elem i j)

theorem continuous_localEmbed : Continuous (localEmbed R K v) :=
  Units.continuous_iff.2 ⟨(continuous_localMat R K v).comp Units.continuous_val,
    (continuous_localMat R K v).comp Units.continuous_coe_inv⟩

theorem continuous_finMat : Continuous (finMat R K) :=
  continuous_matrix fun i j =>
    (continuous_const.prodMk (continuous_id.matrix_elem i j) :
      Continuous fun g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K) =>
        ((((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j, g i j) : AdeleRing R K)))

theorem continuous_finEmbed : Continuous (finEmbed R K) :=
  Units.continuous_iff.2 ⟨(continuous_finMat R K).comp Units.continuous_val,
    (continuous_finMat R K).comp Units.continuous_coe_inv⟩

theorem continuous_placeEmbed : Continuous (placeEmbed K v) :=
  (continuous_finEmbed R K).comp (continuous_localEmbed R K v)

end Continuity

section Split

variable (p : HeightOneSpectrum (𝓞 ℚ))

def projAt : ↥(finiteAdelicGL2Subgroup ℚ) →* GL (Fin 2) (p.adicCompletion ℚ) :=
  (localAt ℚ p).comp (finiteAdelicGL2Subgroup ℚ).subtype

theorem projAt_apply (g : finiteAdelicGL2Subgroup ℚ) : projAt p g = localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) := rfl

theorem continuous_projAt : Continuous (projAt p) :=
  (continuous_localAt ℚ p).comp continuous_subtype_val

theorem placeEmbed_mem (x : GL (Fin 2) (p.adicCompletion ℚ)) : placeEmbed ℚ p x ∈ finiteAdelicGL2Subgroup ℚ :=
  (mem_finiteAdelicGL2Subgroup_iff ℚ _).2 (glArch_finEmbed (𝓞 ℚ) ℚ _)

def embAt : GL (Fin 2) (p.adicCompletion ℚ) →* ↥(finiteAdelicGL2Subgroup ℚ) :=
  (placeEmbed ℚ p).codRestrict _ (placeEmbed_mem p)

@[scoped simp] theorem coe_embAt (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    (embAt p x : AdelicGL2 (𝓞 ℚ) ℚ) = placeEmbed ℚ p x := rfl

theorem continuous_embAt : Continuous (embAt p) :=
  (continuous_placeEmbed (𝓞 ℚ) ℚ p).subtype_mk _

theorem localAt_placeEmbed (x : GL (Fin 2) (p.adicCompletion ℚ)) : localAt ℚ p (placeEmbed ℚ p x) = x := by
  show finComponent (𝓞 ℚ) ℚ p (glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ p x))) = x
  rw [glFin_finEmbed, finComponent_localEmbed_self]

@[scoped simp] theorem projAt_embAt (x : GL (Fin 2) (p.adicCompletion ℚ)) : projAt p (embAt p x) = x :=
  localAt_placeEmbed p x

def awayFrom : Subgroup ↥(finiteAdelicGL2Subgroup ℚ) := (projAt p).ker

theorem mem_awayFrom_iff (g : finiteAdelicGL2Subgroup ℚ) :
    g ∈ awayFrom p ↔ localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := Iff.rfl

theorem isClosed_awayFrom : IsClosed (awayFrom p : Set ↥(finiteAdelicGL2Subgroup ℚ)) :=
  (isClosed_singleton (x := (1 : GL (Fin 2) (p.adicCompletion ℚ)))).preimage (continuous_projAt p)

theorem placeEmbed_mul_comm {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : localAt ℚ p g = 1)
    (x : GL (Fin 2) (p.adicCompletion ℚ)) : placeEmbed ℚ p x * g = g * placeEmbed ℚ p x := by
  have hgp : (finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix ((adeleFin (𝓞 ℚ) ℚ).mapMatrix
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ))) = 1 := congrArg Units.val hg
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  show finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ p x) * _ = _ * finMat (𝓞 ℚ) ℚ (localMat (𝓞 ℚ) ℚ p x)
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?_ ?_
  · rw [map_mul, map_mul, mapMatrix_arch_finMat, one_mul, mul_one]
  · rw [map_mul, map_mul, mapMatrix_fin_finMat]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = p
    · subst hw
      rw [hgp, mul_one, one_mul]
    · rw [mapMatrix_localMat_of_ne (𝓞 ℚ) ℚ p _ hw, one_mul, mul_one]

theorem embAt_mul_comm (g : awayFrom p) (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    embAt p x * (g : finiteAdelicGL2Subgroup ℚ) = (g : finiteAdelicGL2Subgroup ℚ) * embAt p x :=
  Subtype.ext (placeEmbed_mul_comm p g.2 x)

def splitAt : GL (Fin 2) (p.adicCompletion ℚ) × ↥(awayFrom p) ≃* ↥(finiteAdelicGL2Subgroup ℚ) where
  toFun q := embAt p q.1 * (q.2 : finiteAdelicGL2Subgroup ℚ)
  invFun g := (projAt p g, ⟨(embAt p (projAt p g))⁻¹ * g, by
    rw [mem_awayFrom_iff, ← projAt_apply, map_mul, map_inv, projAt_embAt, inv_mul_cancel]⟩)
  left_inv q := by
    obtain ⟨x, g⟩ := q
    have hg : projAt p (g : finiteAdelicGL2Subgroup ℚ) = 1 := g.2
    refine Prod.ext ?_ (Subtype.ext ?_)
    · show projAt p (embAt p x * (g : finiteAdelicGL2Subgroup ℚ)) = x
      rw [map_mul, projAt_embAt, hg, mul_one]
    · show (embAt p (projAt p (embAt p x * (g : finiteAdelicGL2Subgroup ℚ))))⁻¹ *
          (embAt p x * (g : finiteAdelicGL2Subgroup ℚ)) = g
      rw [map_mul, projAt_embAt, hg, mul_one, inv_mul_cancel_left]
  right_inv g := by
    show embAt p (projAt p g) * ((embAt p (projAt p g))⁻¹ * g) = g
    rw [mul_inv_cancel_left]
  map_mul' q r := by
    show embAt p (q.1 * r.1) * ((q.2 : finiteAdelicGL2Subgroup ℚ) * (r.2 : finiteAdelicGL2Subgroup ℚ)) =
      embAt p q.1 * (q.2 : finiteAdelicGL2Subgroup ℚ) * (embAt p r.1 * (r.2 : finiteAdelicGL2Subgroup ℚ))
    rw [map_mul, mul_assoc, mul_assoc, ← mul_assoc (q.2 : finiteAdelicGL2Subgroup ℚ), ← embAt_mul_comm p q.2 r.1,
      mul_assoc]

@[scoped simp] theorem splitAt_apply (q : GL (Fin 2) (p.adicCompletion ℚ) × ↥(awayFrom p)) :
    splitAt p q = embAt p q.1 * (q.2 : finiteAdelicGL2Subgroup ℚ) := rfl

theorem splitAt_symm_apply_fst (g : finiteAdelicGL2Subgroup ℚ) : ((splitAt p).symm g).1 = projAt p g := rfl

theorem coe_splitAt_symm_apply_snd (g : finiteAdelicGL2Subgroup ℚ) :
    (((splitAt p).symm g).2 : finiteAdelicGL2Subgroup ℚ) = (embAt p (projAt p g))⁻¹ * g := rfl

def splitAtHomeo : GL (Fin 2) (p.adicCompletion ℚ) × ↥(awayFrom p) ≃ₜ* ↥(finiteAdelicGL2Subgroup ℚ) :=
  { splitAt p with
    continuous_toFun := ((continuous_embAt p).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
    continuous_invFun := by
      refine (continuous_projAt p).prodMk (Continuous.subtype_mk ?_ _)
      exact (((continuous_embAt p).comp (continuous_projAt p)).inv).mul continuous_id }

@[scoped simp] theorem splitAtHomeo_apply (q : GL (Fin 2) (p.adicCompletion ℚ) × ↥(awayFrom p)) :
    splitAtHomeo p q = splitAt p q := rfl

theorem isEmbedding_embAt : IsEmbedding (embAt p) :=
  IsEmbedding.of_leftInverse (projAt_embAt p) (continuous_projAt p) (continuous_embAt p)

end Split

section Unipotent

theorem mem_range_unipotentGL2Hom_iff {R : Type*} [CommRing R] (g : GL (Fin 2) R) :
    g ∈ (unipotentGL2Hom (R := R)).range ↔
      (g : Matrix (Fin 2) (Fin 2) R) 0 0 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    simp [unipotentGL2Hom]
  · rintro ⟨h00, h10, h11⟩
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) R) 0 1), ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2Hom, h00, h10, h11]

theorem mul_comm_of_mem_range_unipotentGL2Hom {R : Type*} [CommRing R] {a b : GL (Fin 2) R}
    (ha : a ∈ (unipotentGL2Hom (R := R)).range) (hb : b ∈ (unipotentGL2Hom (R := R)).range) : a * b = b * a := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [← map_mul, ← map_mul, mul_comm]

theorem det_eq_one_of_mem_range_unipotentGL2Hom {R : Type*} [CommRing R] {g : GL (Fin 2) R}
    (hg : g ∈ (unipotentGL2Hom (R := R)).range) : Matrix.GeneralLinearGroup.det g = 1 := by
  obtain ⟨a, rfl⟩ := hg
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2Hom, Matrix.det_fin_two_of]

theorem unipotent_eq_unipotentGL2Hom {R : Type*} [Field R] (x : R) :
    unipotent x = unipotentGL2Hom (R := R) (Multiplicative.ofAdd x) :=
  Units.ext rfl

theorem isClosed_range_unipotentGL2Hom {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [T1Space R] : IsClosed (((unipotentGL2Hom (R := R)).range : Subgroup (GL (Fin 2) R)) : Set (GL (Fin 2) R)) := by
  have hc : ∀ i j : Fin 2, Continuous fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have : (((unipotentGL2Hom (R := R)).range : Subgroup (GL (Fin 2) R)) : Set (GL (Fin 2) R)) =
      ((fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 0 0) ⁻¹' {1} ∩
        (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 1 0) ⁻¹' {0}) ∩
        (fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) 1 1) ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, mem_range_unipotentGL2Hom_iff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, and_assoc]
  rw [this]
  exact ((isClosed_singleton.preimage (hc 0 0)).inter (isClosed_singleton.preimage (hc 1 0))).inter
    (isClosed_singleton.preimage (hc 1 1))

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem localAt_mem_range_of_mem_adelicUnipotent {g : AdelicGL2 (𝓞 ℚ) ℚ} (hg : g ∈ adelicUnipotent ℚ) :
    localAt ℚ p g ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range := by
  rw [mem_range_unipotentGL2Hom_iff]
  rw [show adelicUnipotent ℚ = (unipotentGL2Hom (R := AdeleRing (𝓞 ℚ) ℚ)).range from rfl,
    mem_range_unipotentGL2Hom_iff] at hg
  have h : ∀ i j : Fin 2, (localAt ℚ p g : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j =
      (finAdeleEval (𝓞 ℚ) ℚ p) ((adeleFin (𝓞 ℚ) ℚ) ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j)) :=
    fun i j => rfl
  simp only [h, hg.1, hg.2.1, hg.2.2, map_one, map_zero, and_self]

section splice
variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

theorem splice_one_one : splice R K v (1 : FiniteAdeleRing R K) 1 = 1 := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  show (splice R K v (1 : FiniteAdeleRing R K) 1) w = (1 : FiniteAdeleRing R K) w
  by_cases hw : w = v
  · subst hw
    rw [splice_apply_self]
    rfl
  · rw [splice_apply_of_ne R K _ _ _ hw]

theorem splice_zero_zero : splice R K v (0 : FiniteAdeleRing R K) 0 = 0 := by
  refine RestrictedProduct.ext _ _ fun w => ?_
  show (splice R K v (0 : FiniteAdeleRing R K) 0) w = (0 : FiniteAdeleRing R K) w
  by_cases hw : w = v
  · subst hw
    rw [splice_apply_self]
    rfl
  · rw [splice_apply_of_ne R K _ _ _ hw]

end splice

theorem placeEmbed_mem_adelicUnipotent {x : GL (Fin 2) (p.adicCompletion ℚ)}
    (hx : x ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range) : placeEmbed ℚ p x ∈ adelicUnipotent ℚ := by
  rw [show adelicUnipotent ℚ = (unipotentGL2Hom (R := AdeleRing (𝓞 ℚ) ℚ)).range from rfl,
    mem_range_unipotentGL2Hom_iff]
  rw [mem_range_unipotentGL2Hom_iff] at hx
  have h : ∀ i j : Fin 2, (placeEmbed ℚ p x : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j =
      ((((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j,
        splice (𝓞 ℚ) ℚ p ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j)
          ((x : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j)) : AdeleRing (𝓞 ℚ) ℚ)) := fun i j => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [h, hx.1, Matrix.one_apply_eq, Matrix.one_apply_eq, splice_one_one]; rfl
  · rw [h, hx.2.1, Matrix.one_apply_ne (by decide), Matrix.one_apply_ne (by decide), splice_zero_zero]; rfl
  · rw [h, hx.2.2, Matrix.one_apply_eq, Matrix.one_apply_eq, splice_one_one]; rfl

theorem isClosed_finUnipotent :
    IsClosed ((RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) : Set ↥(finiteAdelicGL2Subgroup ℚ)) := by
  rw [show ((RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) : Set ↥(finiteAdelicGL2Subgroup ℚ)) =
      Subtype.val ⁻¹' ((adelicUnipotent ℚ : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ)) from rfl]
  exact isClosed_range_unipotentGL2Hom.preimage continuous_subtype_val

theorem isClosed_localUnipotent :
    IsClosed (((unipotentGL2Hom (R := p.adicCompletion ℚ)).range : Subgroup (GL (Fin 2) (p.adicCompletion ℚ))) :
      Set (GL (Fin 2) (p.adicCompletion ℚ))) :=
  isClosed_range_unipotentGL2Hom

theorem isClosed_finUnipotent_subgroupOf_awayFrom :
    IsClosed ((RSCarrier.finUnipotent.subgroupOf (awayFrom p) : Subgroup ↥(awayFrom p)) : Set ↥(awayFrom p)) := by
  rw [show ((RSCarrier.finUnipotent.subgroupOf (awayFrom p) : Subgroup ↥(awayFrom p)) : Set ↥(awayFrom p)) =
      Subtype.val ⁻¹' ((RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) : Set _) from rfl]
  exact isClosed_finUnipotent.preimage continuous_subtype_val

theorem projAt_mem_localUnipotent (n : RSCarrier.finUnipotent) :
    projAt p (n : finiteAdelicGL2Subgroup ℚ) ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range :=
  localAt_mem_range_of_mem_adelicUnipotent p n.2

theorem embAt_mem_finUnipotent {x : GL (Fin 2) (p.adicCompletion ℚ)}
    (hx : x ∈ (unipotentGL2Hom (R := p.adicCompletion ℚ)).range) : embAt p x ∈ RSCarrier.finUnipotent :=
  placeEmbed_mem_adelicUnipotent p hx

theorem splitAt_symm_snd_mem (n : RSCarrier.finUnipotent) :
    ((splitAt p).symm (n : finiteAdelicGL2Subgroup ℚ)).2 ∈ RSCarrier.finUnipotent.subgroupOf (awayFrom p) := by
  rw [Subgroup.mem_subgroupOf, coe_splitAt_symm_apply_snd]
  exact mul_mem (inv_mem (embAt_mem_finUnipotent p (projAt_mem_localUnipotent p n))) n.2

def splitN : ↥(RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) ≃*
    ↥((unipotentGL2Hom (R := p.adicCompletion ℚ)).range) × ↥(RSCarrier.finUnipotent.subgroupOf (awayFrom p)) where
  toFun n := (⟨projAt p (n : finiteAdelicGL2Subgroup ℚ), projAt_mem_localUnipotent p n⟩,
    ⟨((splitAt p).symm (n : finiteAdelicGL2Subgroup ℚ)).2, splitAt_symm_snd_mem p n⟩)
  invFun q := ⟨splitAt p ((q.1 : GL (Fin 2) (p.adicCompletion ℚ)), (q.2 : ↥(awayFrom p))),
    mul_mem (embAt_mem_finUnipotent p q.1.2) q.2.2⟩
  left_inv n := by
    apply Subtype.ext
    show splitAt p ((splitAt p).symm (n : finiteAdelicGL2Subgroup ℚ)) = n
    exact (splitAt p).apply_symm_apply _
  right_inv q := by
    obtain ⟨x, m⟩ := q
    have h := (splitAt p).symm_apply_apply ((x : GL (Fin 2) (p.adicCompletion ℚ)), (m : ↥(awayFrom p)))
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  map_mul' n m := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show projAt p ((n : finiteAdelicGL2Subgroup ℚ) * m) = projAt p n * projAt p m
      exact map_mul _ _ _
    · show ((splitAt p).symm ((n : finiteAdelicGL2Subgroup ℚ) * m)).2 =
        ((splitAt p).symm (n : finiteAdelicGL2Subgroup ℚ)).2 * ((splitAt p).symm (m : finiteAdelicGL2Subgroup ℚ)).2
      rw [map_mul, Prod.snd_mul]

def splitNHomeo : ↥(RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) ≃ₜ*
    ↥((unipotentGL2Hom (R := p.adicCompletion ℚ)).range) × ↥(RSCarrier.finUnipotent.subgroupOf (awayFrom p)) :=
  { splitN p with
    continuous_toFun := by
      refine Continuous.prodMk (Continuous.subtype_mk ((continuous_projAt p).comp continuous_subtype_val) _)
        (Continuous.subtype_mk (continuous_snd.comp ((splitAtHomeo p).symm.continuous.comp continuous_subtype_val)) _)
    continuous_invFun := by
      refine Continuous.subtype_mk ((splitAtHomeo p).continuous.comp ?_) _
      exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd) }

@[scoped simp] theorem splitNHomeo_apply_fst (n : RSCarrier.finUnipotent) :
    (((splitNHomeo p n).1 : ↥((unipotentGL2Hom (R := p.adicCompletion ℚ)).range)) : GL (Fin 2) (p.adicCompletion ℚ)) =
      projAt p (n : finiteAdelicGL2Subgroup ℚ) := rfl

@[scoped simp] theorem splitNHomeo_apply_snd (n : RSCarrier.finUnipotent) :
    (((splitNHomeo p n).2 : ↥(RSCarrier.finUnipotent.subgroupOf (awayFrom p))) : ↥(awayFrom p)) =
      ((splitAt p).symm (n : finiteAdelicGL2Subgroup ℚ)).2 := rfl

end Unipotent

section Helpers

open MeasureTheory

theorem isMulRightInvariant_of_comm {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (hcomm : ∀ a b : G, a * b = b * a) : μ.IsMulRightInvariant :=
  ⟨fun g => by
    have : (fun h : G => h * g) = fun h => g * h := funext fun h => hcomm h g
    rw [this]
    exact map_mul_left_eq_self μ g⟩

theorem withDensity_map_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (e : α ≃ᵐ β)
    (ν : Measure α) (f : β → ℝ≥0∞) :
    (Measure.map e ν).withDensity f = Measure.map e (ν.withDensity (f ∘ e)) := by
  ext s hs
  rw [withDensity_apply _ hs, e.map_apply, withDensity_apply _ (e.measurable hs),
    e.measurableEmbedding.restrict_map, lintegral_map_equiv]
  rfl

theorem apply_out_mk {G : Type*} [Group G] {H : Subgroup G} {α : Type*} {Φ : G → α}
    (hinv : ∀ (x : H) (g : G), Φ ((x : G) * g) = Φ g) (g : G) :
    Φ (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = Φ g := by
  have h : (MulAction.orbitRel H G) (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out g :=
    Quotient.exact (Quotient.out_eq _)
  obtain ⟨x, hx⟩ := MulAction.orbitRel_apply.1 h
  rw [← hx]
  exact hinv x g

theorem measurable_comp_out {G : Type*} [Group G] [MeasurableSpace G] {H : Subgroup G} {α : Type*}
    [MeasurableSpace α] {Φ : G → α} (hΦ : Measurable Φ) (hinv : ∀ (x : H) (g : G), Φ ((x : G) * g) = Φ g) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => Φ q.out := by
  refine measurable_from_quotient.2 ?_
  have : (fun q : MulAction.orbitRel.Quotient H G => Φ q.out) ∘ Quotient.mk'' = Φ :=
    funext fun g => apply_out_mk hinv g
  rw [this]
  exact hΦ

theorem measurable_weight {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) : Measurable (HaarQuotient.weight H μH) := by
  unfold HaarQuotient.weight
  split_ifs with h
  · refine Measurable.ennreal_tsum fun n => ?_
    exact measurable_const.mul ((measurable_const.indicator isOpen_interior.measurableSet))
  · exact measurable_const

theorem measurable_density {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (μH : Measure H) [SFinite μH] : Measurable (HaarQuotient.density H μH) := by
  have hw := measurable_weight H μH
  have h2 : Measurable fun z : G × H => HaarQuotient.weight H μH ((z.2 : G) * z.1) :=
    hw.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst).measurable
  unfold HaarQuotient.density
  exact hw.div h2.lintegral_prod_right'

theorem integral_withDensity_eq_of_admissible {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρc : ∀ g : G, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = 1)
    (Φ : G → ℂ) (hΦ : Measurable Φ) (hinv : ∀ (x : H) (g : G), Φ ((x : G) * g) = Φ g) :
    ∫ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH)) = ∫ g, Φ g ∂(μ.withDensity ρ) := by
  have hmk : Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) (μ.withDensity ρ) =
      Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)
        (μ.withDensity (HaarQuotient.density H μH)) := by
    rw [HaarQuotient.map_mk_withDensity_eq_smul_measure μ H hH μH ρ hρ 1 hρc, one_smul]
    rfl
  set Ψ : MulAction.orbitRel.Quotient H G → ℂ := fun q => Φ q.out with hΨ
  have hΨm : Measurable Ψ := measurable_comp_out hΦ hinv
  have hΦΨ : Φ = fun g => Ψ (Quotient.mk'' g) := funext fun g => (apply_out_mk hinv g).symm
  rw [hΦΨ]
  change ∫ g, Ψ (Quotient.mk'' g) ∂_ = ∫ g, Ψ (Quotient.mk'' g) ∂_
  rw [← integral_map measurable_quotient_mk''.aemeasurable hΨm.stronglyMeasurable.aestronglyMeasurable,
    ← integral_map measurable_quotient_mk''.aemeasurable hΨm.stronglyMeasurable.aestronglyMeasurable, hmk]

end Helpers

section LIntegralHelpers

open MeasureTheory

theorem lintegral_withDensity_eq_of_admissible {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (ρ : G → ℝ≥0∞) (hρ : Measurable ρ) (hρc : ∀ g : G, ∫⁻ x : H, ρ ((x : G) * g) ∂μH = 1)
    (Φ : G → ℝ≥0∞) (hΦ : Measurable Φ) (hinv : ∀ (x : H) (g : G), Φ ((x : G) * g) = Φ g) :
    ∫⁻ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH)) = ∫⁻ g, Φ g ∂(μ.withDensity ρ) := by
  have hmk : Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G) (μ.withDensity ρ) =
      Measure.map (Quotient.mk'' : G → MulAction.orbitRel.Quotient H G)
        (μ.withDensity (HaarQuotient.density H μH)) := by
    rw [HaarQuotient.map_mk_withDensity_eq_smul_measure μ H hH μH ρ hρ 1 hρc, one_smul]
    rfl
  set Ψ : MulAction.orbitRel.Quotient H G → ℝ≥0∞ := fun q => Φ q.out with hΨ
  have hΨm : Measurable Ψ := measurable_comp_out hΦ hinv
  have hΦΨ : Φ = fun g => Ψ (Quotient.mk'' g) := funext fun g => (apply_out_mk hinv g).symm
  rw [hΦΨ]
  change ∫⁻ g, Ψ (Quotient.mk'' g) ∂_ = ∫⁻ g, Ψ (Quotient.mk'' g) ∂_
  rw [← lintegral_map hΨm measurable_quotient_mk'', ← lintegral_map hΨm measurable_quotient_mk'', hmk]

end LIntegralHelpers

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem finUnipotent_comm (a b : (RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ))) : a * b = b * a :=
  Subtype.ext (Subtype.ext (mul_comm_of_mem_range_unipotentGL2Hom a.2 b.2))

theorem localUnipotent_comm (a b : ((unipotentGL2Hom (R := p.adicCompletion ℚ)).range)) : a * b = b * a :=
  Subtype.ext (mul_comm_of_mem_range_unipotentGL2Hom a.2 b.2)

theorem continuous_det_adelic :
    Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => Matrix.GeneralLinearGroup.det g :=
  Units.continuous_iff.2 ⟨(Units.continuous_val.matrix_det :
      Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det),
    (Units.continuous_coe_inv.matrix_det :
      Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => ((g⁻¹ : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det)⟩

theorem continuous_ideleNorm_det :
    Continuous fun g : AdelicGL2 (𝓞 ℚ) ℚ => ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) :=
  (NumberField.TateGlobal.continuous_ideleNorm ℚ).comp continuous_det_adelic

theorem continuous_modulus_det :
    Continuous fun y : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) := by
  have h : (fun y : GL (Fin 2) (p.adicCompletion ℚ) =>
      ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ))) =
      fun y => ideleNorm ℚ (Matrix.GeneralLinearGroup.det (placeEmbed ℚ p y)) :=
    funext fun y => (NumberField.TateGlobal.ideleNorm_det_placeEmbed p y).symm
  rw [h]
  exact continuous_ideleNorm_det.comp (continuous_placeEmbed (𝓞 ℚ) ℚ p)

theorem measurable_normWeight (t : ℝ) :
    Measurable fun g : finiteAdelicGL2Subgroup ℚ =>
      ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ t) :=
  ENNReal.measurable_ofReal.comp
    (((continuous_ideleNorm_det.comp continuous_subtype_val).measurable).pow_const t)

theorem lintegral_swap
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (Φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℝ≥0∞)
    (hΦ' : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), Φ' (g * placeEmbed ℚ p x) = Φ' g)
    (hN' : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      Φ' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        Φ' (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hΦ'm : Measurable fun g : finiteAdelicGL2Subgroup ℚ => Φ' (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (t : ℝ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure]
      (φ φ₀ : GL (Fin 2) (p.adicCompletion ℚ) → ℝ≥0∞), Measurable φ → Measurable φ₀ →
      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), φ (unipotent x * g) = φ g) →
      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), φ₀ (unipotent x * g) = φ₀ g) →
      (∫⁻ g : finiteAdelicGL2Subgroup ℚ, φ (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ)) * Φ' (g : AdelicGL2 (𝓞 ℚ) ℚ) *
            ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ t)
          ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))) *
        (∫⁻ y : GL (Fin 2) (p.adicCompletion ℚ), φ₀ y *
            ENNReal.ofReal (((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) :
              p.adicCompletion ℚ) : ℝ)) ^ t)
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) =
      (∫⁻ g : finiteAdelicGL2Subgroup ℚ, φ₀ (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ)) * Φ' (g : AdelicGL2 (𝓞 ℚ) ℚ) *
            ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ t)
          ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN))) *
        (∫⁻ y : GL (Fin 2) (p.adicCompletion ℚ), φ y *
            ENNReal.ofReal (((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) :
              p.adicCompletion ℚ) : ℝ)) ^ t)
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) := by
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  intro μ₂ _ μN₂ _ φ φ₀ hφm hφ₀m hn hn₀

  haveI : SecondCountableTopology ↥(finiteAdelicGL2Subgroup ℚ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace ↥(finiteAdelicGL2Subgroup ℚ) :=
    (isClosed_finiteAdelicGL2Subgroup ℚ).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace ↥(finiteAdelicGL2Subgroup ℚ) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : LocallyCompactSpace ↥(awayFrom p) := (isClosed_awayFrom p).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology ↥(awayFrom p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace ↥(awayFrom p) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : LocallyCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ p
  haveI : SecondCountableTopology (GL (Fin 2) (p.adicCompletion ℚ)) := (isEmbedding_embAt p).secondCountableTopology
  haveI : SigmaCompactSpace (GL (Fin 2) (p.adicCompletion ℚ)) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : LocallyCompactSpace ↥((unipotentGL2Hom (R := p.adicCompletion ℚ)).range) :=
    (isClosed_localUnipotent p).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology ↥((unipotentGL2Hom (R := p.adicCompletion ℚ)).range) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace ↥((unipotentGL2Hom (R := p.adicCompletion ℚ)).range) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : LocallyCompactSpace ↥(RSCarrier.finUnipotent.subgroupOf (awayFrom p)) :=
    (isClosed_finUnipotent_subgroupOf_awayFrom p).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology ↥(RSCarrier.finUnipotent.subgroupOf (awayFrom p)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace ↥(RSCarrier.finUnipotent.subgroupOf (awayFrom p)) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : LocallyCompactSpace ↥(RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) :=
    isClosed_finUnipotent.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology ↥(RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace ↥(RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  haveI : SigmaFinite μN := Measure.IsHaarMeasure.sigmaFinite μN
  haveI : SigmaFinite μ₂ := Measure.IsHaarMeasure.sigmaFinite μ₂
  haveI : SigmaFinite μN₂ := Measure.IsHaarMeasure.sigmaFinite μN₂
  haveI : μN.IsMulRightInvariant := isMulRightInvariant_of_comm μN finUnipotent_comm
  haveI : μN₂.IsMulRightInvariant := isMulRightInvariant_of_comm μN₂ (localUnipotent_comm p)

  obtain ⟨μ', hμ', -, hsplit⟩ :=
    MeasureTheory.Measure.exists_isHaarMeasure_map_continuousMulEquiv_eq_prod μ μ₂ (splitAtHomeo p).symm
  obtain ⟨μN', hμN', hμN'r, hNsplit⟩ :=
    MeasureTheory.Measure.exists_isHaarMeasure_map_continuousMulEquiv_eq_prod μN μN₂ (splitNHomeo p)
  haveI := hμ'
  haveI := hμN'
  haveI : μN'.IsMulRightInvariant := hμN'r inferInstance
  haveI : SigmaFinite μ' := Measure.IsHaarMeasure.sigmaFinite μ'
  haveI : SigmaFinite μN' := Measure.IsHaarMeasure.sigmaFinite μN'
  haveI : SFinite μ' := instSFiniteOfSigmaFinite
  haveI : SFinite μN' := instSFiniteOfSigmaFinite
  haveI : SFinite μ₂ := instSFiniteOfSigmaFinite
  haveI : SFinite μN₂ := instSFiniteOfSigmaFinite
  haveI : SFinite μ := instSFiniteOfSigmaFinite
  haveI : SFinite μN := instSFiniteOfSigmaFinite

  let d : GL (Fin 2) (p.adicCompletion ℚ) → ℝ≥0∞ :=
    HaarQuotient.density ((unipotentGL2Hom (R := p.adicCompletion ℚ)).range) μN₂
  let D' : ↥(awayFrom p) → ℝ≥0∞ := HaarQuotient.density (RSCarrier.finUnipotent.subgroupOf (awayFrom p)) μN'
  let Dx : ↥(finiteAdelicGL2Subgroup ℚ) → ℝ≥0∞ := fun g => d (projAt p g) * D' ((splitAtHomeo p).symm g).2
  have hd : Measurable d := measurable_density _ _
  have hD' : Measurable D' := measurable_density _ _
  have hDx : Measurable Dx :=
    (hd.comp (continuous_projAt p).measurable).mul
      (hD'.comp (continuous_snd.comp (splitAtHomeo p).symm.continuous).measurable)
  have hadm : ∀ g : finiteAdelicGL2Subgroup ℚ,
      ∫⁻ n : ↥(RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)), Dx ((n : finiteAdelicGL2Subgroup ℚ) * g) ∂μN = 1 := by
    intro g
    let Fg : ↥((unipotentGL2Hom (R := p.adicCompletion ℚ)).range) × ↥(RSCarrier.finUnipotent.subgroupOf (awayFrom p)) → ℝ≥0∞ :=
      fun q => d ((q.1 : GL (Fin 2) (p.adicCompletion ℚ)) * projAt p g) * D' ((q.2 : ↥(awayFrom p)) * ((splitAtHomeo p).symm g).2)
    have hpt : (fun n : ↥(RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) => Dx ((n : finiteAdelicGL2Subgroup ℚ) * g)) =
        fun n => Fg (splitNHomeo p n) := by
      funext n
      show d (projAt p ((n : finiteAdelicGL2Subgroup ℚ) * g)) * D' ((splitAtHomeo p).symm ((n : finiteAdelicGL2Subgroup ℚ) * g)).2 =
        d (projAt p (n : finiteAdelicGL2Subgroup ℚ) * projAt p g) *
          D' (((splitAt p).symm (n : finiteAdelicGL2Subgroup ℚ)).2 * ((splitAtHomeo p).symm g).2)
      rw [map_mul, map_mul, Prod.snd_mul]
      rfl
    rw [hpt]
    let eN := (splitNHomeo p).toHomeomorph.toMeasurableEquiv
    have h1 : ∫⁻ n, Fg (splitNHomeo p n) ∂μN = ∫⁻ q, Fg q ∂(Measure.map (splitNHomeo p) μN) := by
      rw [show (⇑(splitNHomeo p) : _ → _) = ⇑eN from rfl, lintegral_map_equiv]
    have hf : AEMeasurable (fun x : ↥((unipotentGL2Hom (R := p.adicCompletion ℚ)).range) =>
        d ((x : GL (Fin 2) (p.adicCompletion ℚ)) * projAt p g)) μN₂ :=
      (hd.comp (continuous_subtype_val.mul continuous_const).measurable).aemeasurable
    have hg : AEMeasurable (fun m : ↥(RSCarrier.finUnipotent.subgroupOf (awayFrom p)) =>
        D' ((m : ↥(awayFrom p)) * ((splitAtHomeo p).symm g).2)) μN' :=
      (hD'.comp (continuous_subtype_val.mul continuous_const).measurable).aemeasurable
    rw [h1, hNsplit, show ∫⁻ q, Fg q ∂(μN₂.prod μN') = _ from lintegral_prod_mul hf hg,
      HaarQuotient.lintegral_density_mul_eq_one _ (isClosed_localUnipotent p) μN₂ (projAt p g),
      HaarQuotient.lintegral_density_mul_eq_one _ (isClosed_finUnipotent_subgroupOf_awayFrom p) μN' _, one_mul]

  let Θ := (splitAtHomeo p).toHomeomorph.toMeasurableEquiv
  have hμ : Measure.map Θ (μ₂.prod μ') = μ := by
    rw [← hsplit]
    exact MeasurableEquiv.map_map_symm Θ
  have hDxΘ : Dx ∘ Θ = fun q => d q.1 * D' q.2 := by
    funext q
    show d (projAt p (splitAt p q)) * D' ((splitAtHomeo p).symm (splitAtHomeo p q)).2 = d q.1 * D' q.2
    rw [(splitAtHomeo p).symm_apply_apply]
    congr 2
    show ((splitAt p).symm (splitAt p q)).1 = q.1
    rw [MulEquiv.symm_apply_apply]

  let wloc : GL (Fin 2) (p.adicCompletion ℚ) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) :
      p.adicCompletion ℚ) : ℝ)) ^ t)
  have hwloc : Measurable wloc := ENNReal.measurable_ofReal.comp ((continuous_modulus_det p).measurable.pow_const t)
  let A : ↥(awayFrom p) → ℝ≥0∞ := fun k => Φ' ((k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) *
    ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det ((k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) ^ t)
  have hA : Measurable A :=
    (hΦ'm.comp continuous_subtype_val.measurable).mul ((measurable_normWeight t).comp continuous_subtype_val.measurable)

  have hfac : ∀ (ψ : GL (Fin 2) (p.adicCompletion ℚ) → ℝ≥0∞), Measurable ψ →
      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), ψ (unipotent x * g) = ψ g) →
      ∫⁻ g : finiteAdelicGL2Subgroup ℚ, ψ (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ)) * Φ' (g : AdelicGL2 (𝓞 ℚ) ℚ) *
            ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ t)
          ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) =
        (∫⁻ y, ψ y * wloc y ∂(μ₂.withDensity d)) * ∫⁻ k, A k ∂(μ'.withDensity D') := by
    intro ψ hψm hψn
    let I : ↥(finiteAdelicGL2Subgroup ℚ) → ℝ≥0∞ := fun g =>
      ψ (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ)) * Φ' (g : AdelicGL2 (𝓞 ℚ) ℚ) *
        ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ t)
    have hIm : Measurable I :=
      ((hψm.comp (continuous_projAt p).measurable).mul hΦ'm).mul (measurable_normWeight t)
    have hIinv : ∀ (n : ↥(RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ))) (g : finiteAdelicGL2Subgroup ℚ),
        I ((n : finiteAdelicGL2Subgroup ℚ) * g) = I g := by
      intro n g
      obtain ⟨a, ha⟩ := localAt_mem_range_of_mem_adelicUnipotent p n.2
      change unipotentGL2Hom a = localAt ℚ p ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) at ha
      have hng : (((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) =
          ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * (g : AdelicGL2 (𝓞 ℚ) ℚ) := rfl
      have hloc : localAt ℚ p (((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * (g : AdelicGL2 (𝓞 ℚ) ℚ)) =
          unipotent a.toAdd * localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
        rw [map_mul, ← ha, unipotent_eq_unipotentGL2Hom]
        rfl
      have hdet : Matrix.GeneralLinearGroup.det (((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * (g : AdelicGL2 (𝓞 ℚ) ℚ)) =
          Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
        rw [map_mul, det_eq_one_of_mem_range_unipotentGL2Hom (g := ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) n.2,
          one_mul]
      show ψ (localAt ℚ p ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)) *
          Φ' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det
            ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)) ^ t) = _
      rw [hN' n g, hng, hloc, hψn, hdet]
    rw [lintegral_withDensity_eq_of_admissible μ RSCarrier.finUnipotent isClosed_finUnipotent μN Dx hDx hadm I hIm hIinv,
      ← hμ, withDensity_map_equiv Θ _ Dx, lintegral_map_equiv, hDxΘ, ← prod_withDensity hd hD']
    have hIΘ : (fun q : GL (Fin 2) (p.adicCompletion ℚ) × ↥(awayFrom p) => I (Θ q)) = fun q =>
        (ψ q.1 * wloc q.1) * A q.2 := by
      funext q
      obtain ⟨x, k⟩ := q
      have hk : localAt ℚ p ((k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := (mem_awayFrom_iff p _).1 k.2
      show ψ (localAt ℚ p (placeEmbed ℚ p x * ((k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) *
          Φ' (placeEmbed ℚ p x * ((k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) *
          ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det
            (placeEmbed ℚ p x * ((k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) ^ t) = _
      have e1 : localAt ℚ p (placeEmbed ℚ p x * ((k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) = x := by
        rw [map_mul, localAt_placeEmbed, hk, mul_one]
      have e2 : Φ' (placeEmbed ℚ p x * ((k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) =
          Φ' ((k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) := by
        rw [placeEmbed_mul_comm p hk, hΦ']
      have e4 : ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det
            (placeEmbed ℚ p x * ((k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ))) ^ t) =
          wloc x * ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det
            ((k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ)) ^ t) := by
        rw [map_mul, ideleNorm_mul, NumberField.TateGlobal.ideleNorm_det_placeEmbed,
          Real.mul_rpow (NNReal.coe_nonneg _) (ideleNorm_pos _).le,
          ENNReal.ofReal_mul (Real.rpow_nonneg (NNReal.coe_nonneg _) _)]
      rw [e1, e2, e4]
      show ψ x * Φ' ((k : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) * (wloc x * _) = ψ x * wloc x * A k
      simp only [A]
      ring
    rw [hIΘ, lintegral_prod_mul (μ := μ₂.withDensity d) (ν := μ'.withDensity D')
      ((hψm.fun_mul hwloc).aemeasurable) hA.aemeasurable]

  rw [hfac φ hφm hn, hfac φ₀ hφ₀m hn₀]
  show (∫⁻ y, φ y * wloc y ∂(μ₂.withDensity d)) * (∫⁻ k, A k ∂(μ'.withDensity D')) * (∫⁻ y, φ₀ y * wloc y ∂(μ₂.withDensity d)) =
    (∫⁻ y, φ₀ y * wloc y ∂(μ₂.withDensity d)) * (∫⁻ k, A k ∂(μ'.withDensity D')) * (∫⁻ y, φ y * wloc y ∂(μ₂.withDensity d))
  ring

end Main

theorem measurable_cpowWeight (s : ℂ) :
    Measurable fun g : finiteAdelicGL2Subgroup ℚ =>
      ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)) :=
  (Complex.continuous_ofReal.comp (continuous_ideleNorm_det.comp continuous_subtype_val)).measurable.pow_const _

section Transfer

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem lt_top_of_mul_eq_mul {a b c d : ℝ≥0∞} (h : a * b = c * d) (hb : b ≠ 0) (hc : c < ⊤) (hd : d < ⊤) :
    a < ⊤ := by
  have hcd : c * d < ⊤ := ENNReal.mul_lt_top hc hd
  by_contra ha
  rw [not_lt, top_le_iff] at ha
  rw [ha, ENNReal.top_mul hb] at h
  exact hcd.ne h.symm

theorem integrable_transfer
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (W F W₀ F₀ W' F' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (w f w₀ f₀ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W g = w (localAt ℚ p g) * W' g)
    (hW₀ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W₀ g = w₀ (localAt ℚ p g) * W' g)
    (hF : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, F g = f (localAt ℚ p g) * F' g)
    (hF₀ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, F₀ g = f₀ (localAt ℚ p g) * F' g)
    (hW' : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), W' (g * placeEmbed ℚ p x) = W' g)
    (hF' : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), F' (g * placeEmbed ℚ p x) = F' g)
    (hN' : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      ‖W' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)‖ =
        ‖W' (g : AdelicGL2 (𝓞 ℚ) ℚ) * F' (g : AdelicGL2 (𝓞 ℚ) ℚ)‖)
    (hn : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      ‖w (unipotent x * g) * f (unipotent x * g)‖ = ‖w g * f g‖)
    (hn₀ : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      ‖w₀ (unipotent x * g) * f₀ (unipotent x * g)‖ = ‖w₀ g * f₀ g‖)
    (hWFm' : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W' g * F' g)
    (hWFm : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W g * F g)
    (s : ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      Measurable (fun y => w y * f y) → Measurable (fun y => w₀ y * f₀ y) →
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ => (W₀ g * F₀ g) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)))
        (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) →
      (∫⁻ y : GL (Fin 2) (p.adicCompletion ℚ), ‖(w₀ y * f₀ y) *
          ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ≠ 0 →
      (∫⁻ y : GL (Fin 2) (p.adicCompletion ℚ), ‖(w y * f y) *
          ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) < ⊤ →
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)))
        (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) := by
  letI : MeasurableSpace (GL (Fin 2) (p.adicCompletion ℚ)) := localGLBorel ℚ p
  haveI : BorelSpace (GL (Fin 2) (p.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ p
  intro μ₂ _ μN₂ _ hwfm hwf₀m hint hne hfin
  set t : ℝ := (s - 1 / 2).re with ht

  let φ : GL (Fin 2) (p.adicCompletion ℚ) → ℝ≥0∞ := fun y => ‖w y * f y‖ₑ
  let φ₀ : GL (Fin 2) (p.adicCompletion ℚ) → ℝ≥0∞ := fun y => ‖w₀ y * f₀ y‖ₑ
  let Φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℝ≥0∞ := fun g => ‖W' g * F' g‖ₑ
  have hφm : Measurable φ := hwfm.enorm
  have hφ₀m : Measurable φ₀ := hwf₀m.enorm
  have hΦ'm : Measurable fun g : finiteAdelicGL2Subgroup ℚ => Φ' (g : AdelicGL2 (𝓞 ℚ) ℚ) := hWFm'.enorm
  have hΦ'x : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), Φ' (g * placeEmbed ℚ p x) = Φ' g := by
    intro x g; show ‖W' (g * placeEmbed ℚ p x) * F' (g * placeEmbed ℚ p x)‖ₑ = ‖W' g * F' g‖ₑ; rw [hW', hF']
  have hΦ'N : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      Φ' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) = Φ' (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
    intro n g
    show ‖_‖ₑ = ‖_‖ₑ
    rw [← ofReal_norm, ← ofReal_norm, hN']
  have hφn : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), φ (unipotent x * g) = φ g := by
    intro x g; show ‖_‖ₑ = ‖_‖ₑ; rw [← ofReal_norm, ← ofReal_norm, hn]
  have hφ₀n : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), φ₀ (unipotent x * g) = φ₀ g := by
    intro x g; show ‖_‖ₑ = ‖_‖ₑ; rw [← ofReal_norm, ← ofReal_norm, hn₀]

  have hglob : ∀ (Wx Fx : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (wx fx : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Wx g = wx (localAt ℚ p g) * W' g) →
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Fx g = fx (localAt ℚ p g) * F' g) →
      ∀ g : finiteAdelicGL2Subgroup ℚ,
        ‖(Wx g * Fx g) * ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2))‖ₑ =
          ‖wx (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ)) * fx (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))‖ₑ * Φ' (g : AdelicGL2 (𝓞 ℚ) ℚ) *
            ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ t) := by
    intro Wx Fx wx fx hWx hFx g
    have e1 : (Wx g * Fx g) * ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)) =
        ((wx (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ)) * fx (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ))) * (W' g * F' g)) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)) := by
      rw [hWx, hFx]; ring
    rw [e1, enorm_mul, enorm_mul, ← ofReal_norm ((ideleNorm ℚ _ : ℂ) ^ (s - 1 / 2)),
      Complex.norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos _), ← ht]
  have hloc : ∀ (wx fx : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (y : GL (Fin 2) (p.adicCompletion ℚ)),
      ‖(wx y * fx y) * ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ =
        ‖wx y * fx y‖ₑ * ENNReal.ofReal (((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) :
          p.adicCompletion ℚ) : ℝ)) ^ t) := by
    intro wx fx y
    rw [enorm_mul, ← ofReal_norm ((_ : ℂ) ^ (s - 1 / 2))]
    have hpos : (0 : ℝ) < ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ)) :=
      NNReal.coe_pos.2 (modulus_pos (Units.ne_zero _))
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, ← ht]

  have hswap := lintegral_swap p μ μN Φ' hΦ'x hΦ'N hΦ'm t μ₂ μN₂ φ φ₀ hφm hφ₀m hφn hφ₀n

  have hI : ∀ (Wx Fx : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (wx fx : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Wx g = wx (localAt ℚ p g) * W' g) →
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Fx g = fx (localAt ℚ p g) * F' g) →
      ∫⁻ g : finiteAdelicGL2Subgroup ℚ, ‖(Wx g * Fx g) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2))‖ₑ
        ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) =
      ∫⁻ g : finiteAdelicGL2Subgroup ℚ, (fun y => ‖wx y * fx y‖ₑ) (localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ)) * Φ' (g : AdelicGL2 (𝓞 ℚ) ℚ) *
            ENNReal.ofReal (ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ t)
        ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) :=
    fun Wx Fx wx fx hWx hFx => lintegral_congr fun g => hglob Wx Fx wx fx hWx hFx g
  have hL : ∀ (wx fx : GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
      ∫⁻ y : GL (Fin 2) (p.adicCompletion ℚ), ‖(wx y * fx y) *
          ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) =
      ∫⁻ y : GL (Fin 2) (p.adicCompletion ℚ), (fun y => ‖wx y * fx y‖ₑ) y *
            ENNReal.ofReal (((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) :
              p.adicCompletion ℚ) : ℝ)) ^ t)
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂)) :=
    fun wx fx => lintegral_congr fun y => hloc wx fx y
  rw [hL w₀ f₀] at hne
  rw [hL w f] at hfin
  have hint' := hint.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm, hI W₀ F₀ w₀ f₀ hW₀ hF₀] at hint'

  refine ⟨(hWFm.mul (measurable_cpowWeight s)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, hI W F w f hW hF]
  exact lt_top_of_mul_eq_mul hswap hne hint' hfin

end Transfer

end KcFinCellTonelli
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integrable_finCell_of_integrable_of_factorsAt.KcFinCellTonelli"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_integrable_finCell_of_integrable_of_factorsAt.KcFinCellTonelli"

open KcFinCellTonelli in
open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker in

theorem solution
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (p : HeightOneSpectrum (𝓞 ℚ))
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure]
    (W F W₀ F₀ W' F' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (w f w₀ f₀ : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W g = w (localAt ℚ p g) * W' g)
    (hW₀ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W₀ g = w₀ (localAt ℚ p g) * W' g)
    (hF : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, F g = f (localAt ℚ p g) * F' g)
    (hF₀ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, F₀ g = f₀ (localAt ℚ p g) * F' g)
    (hW' : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), W' (g * placeEmbed ℚ p x) = W' g)
    (hF' : ∀ (x : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), F' (g * placeEmbed ℚ p x) = F' g)
    (hN' : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      ‖W' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F' ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ)‖ =
        ‖W' (g : AdelicGL2 (𝓞 ℚ) ℚ) * F' (g : AdelicGL2 (𝓞 ℚ) ℚ)‖)
    (hn : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      ‖w (unipotent x * g) * f (unipotent x * g)‖ = ‖w g * f g‖)
    (hn₀ : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      ‖w₀ (unipotent x * g) * f₀ (unipotent x * g)‖ = ‖w₀ g * f₀ g‖)
    (hWFm' : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W' g * F' g)
    (hWFm : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W g * F g)
    (s : ℂ) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [μ₂.IsHaarMeasure]
      (μN₂ : Measure ↥(unipotentGL2Hom (R := p.adicCompletion ℚ)).range) [μN₂.IsHaarMeasure],
      Measurable (fun y => w y * f y) → Measurable (fun y => w₀ y * f₀ y) →
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ => (W₀ g * F₀ g) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)))
        (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) →
      (∫⁻ y : GL (Fin 2) (p.adicCompletion ℚ), ‖(w₀ y * f₀ y) *
          ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) ≠ 0 →
      (∫⁻ y : GL (Fin 2) (p.adicCompletion ℚ), ‖(w y * f y) *
          ((modulus ((Matrix.GeneralLinearGroup.det y : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)‖ₑ
        ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := p.adicCompletion ℚ)).range μN₂))) < ⊤ →
      Integrable (fun g : finiteAdelicGL2Subgroup ℚ => (W g * F g) *
          ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ (s - 1 / 2)))
        (μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) :=
  KcFinCellTonelli.integrable_transfer p μ μN W F W₀ F₀ W' F' w f w₀ f₀ hW hW₀ hF hF₀ hW' hF' hN' hn hn₀ hWFm' hWFm s

end S_LanglandsTunnell_RankinSelberg_integrable_finCell_of_integrable_of_factorsAt
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_integrable_finCell_of_integrable_of_factorsAt (solution)
