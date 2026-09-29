-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e9dcfbdd-af13-5d99-808c-b820be07b939

import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
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

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory UnramifiedWhittaker AdelicDock
open NumberField.AdelicLevel Topology NumberField.TateGlobal LanglandsTunnell.TateLocal
open LanglandsTunnell.RankinSelberg
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace Ws23Swap

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

section Main

variable (p : HeightOneSpectrum (𝓞 ℚ))

theorem finUnipotent_comm (a b : (RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ))) : a * b = b * a :=
  Subtype.ext (Subtype.ext (mul_comm_of_mem_range_unipotentGL2Hom a.2 b.2))

theorem localUnipotent_comm (a b : ((unipotentGL2Hom (R := p.adicCompletion ℚ)).range)) : a * b = b * a :=
  Subtype.ext (mul_comm_of_mem_range_unipotentGL2Hom a.2 b.2)

theorem ratArchGL2_placeEmbed' (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    LanglandsTunnell.ratArchGL2 (placeEmbed ℚ p x) = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [show glArch (𝓞 ℚ) ℚ (placeEmbed ℚ p x) = 1 from glArch_finEmbed (𝓞 ℚ) ℚ _, map_one, map_one]

theorem finFactor_placeEmbed (x : GL (Fin 2) (p.adicCompletion ℚ)) :
    RSCarrier.finFactor (placeEmbed ℚ p x) = embAt p x := by
  apply Subtype.ext
  show (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (LanglandsTunnell.ratArchGL2 (placeEmbed ℚ p x)))⁻¹ *
      placeEmbed ℚ p x = placeEmbed ℚ p x
  rw [ratArchGL2_placeEmbed', map_one, inv_one, one_mul]

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

end Main

end Ws23Swap
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed.Ws23Swap"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed.Ws23Swap"

open scoped ENNReal in
theorem solution
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)]
    (v : HeightOneSpectrum (𝓞 ℚ))
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure RSCarrier.finUnipotent) [μN.IsHaarMeasure] :
    letI := localGLBorel ℚ v
    haveI := borelSpace_localGLBorel ℚ v
    ∀ (μv : Measure (GL (Fin 2) (v.adicCompletion ℚ))) [μv.IsHaarMeasure]
      (μNv : Measure ↥(unipotentGL2Hom (R := v.adicCompletion ℚ)).range) [μNv.IsHaarMeasure],
    ∃ μ' : Measure (finiteAdelicGL2Subgroup ℚ), SFinite μ' ∧
      (∀ᵐ g' : finiteAdelicGL2Subgroup ℚ ∂μ', localAt ℚ v (g' : AdelicGL2 (𝓞 ℚ) ℚ) = 1) ∧
      ∀ Φ : finiteAdelicGL2Subgroup ℚ → ℝ≥0∞, Measurable Φ →
        (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), Φ ((n : finiteAdelicGL2Subgroup ℚ) * g) = Φ g) →
        ∫⁻ g, Φ g ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) =
          ∫⁻ g', ∫⁻ x, Φ (g' * RSCarrier.finFactor (UnramifiedWhittaker.placeEmbed ℚ v x))
              ∂(μv.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μNv))
            ∂μ' := by
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion ℚ)) := localGLBorel ℚ v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion ℚ)) := borelSpace_localGLBorel ℚ v
  intro μ₂ _ μN₂ _
  open Ws23Swap in

  haveI : SecondCountableTopology ↥(finiteAdelicGL2Subgroup ℚ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace ↥(finiteAdelicGL2Subgroup ℚ) :=
    (isClosed_finiteAdelicGL2Subgroup ℚ).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SigmaCompactSpace ↥(finiteAdelicGL2Subgroup ℚ) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : LocallyCompactSpace ↥(awayFrom v) := (isClosed_awayFrom v).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology ↥(awayFrom v) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace ↥(awayFrom v) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := locallyCompactSpace_localGL ℚ v
  haveI : SecondCountableTopology (GL (Fin 2) (v.adicCompletion ℚ)) := (isEmbedding_embAt v).secondCountableTopology
  haveI : SigmaCompactSpace (GL (Fin 2) (v.adicCompletion ℚ)) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : LocallyCompactSpace ↥((unipotentGL2Hom (R := v.adicCompletion ℚ)).range) :=
    (isClosed_localUnipotent v).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology ↥((unipotentGL2Hom (R := v.adicCompletion ℚ)).range) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace ↥((unipotentGL2Hom (R := v.adicCompletion ℚ)).range) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : LocallyCompactSpace ↥(RSCarrier.finUnipotent.subgroupOf (awayFrom v)) :=
    (isClosed_finUnipotent_subgroupOf_awayFrom v).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology ↥(RSCarrier.finUnipotent.subgroupOf (awayFrom v)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace ↥(RSCarrier.finUnipotent.subgroupOf (awayFrom v)) :=
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
  haveI : μN₂.IsMulRightInvariant := isMulRightInvariant_of_comm μN₂ (localUnipotent_comm v)

  obtain ⟨μ', hμ', -, hsplit⟩ :=
    MeasureTheory.Measure.exists_isHaarMeasure_map_continuousMulEquiv_eq_prod μ μ₂ (splitAtHomeo v).symm
  obtain ⟨μN', hμN', hμN'r, hNsplit⟩ :=
    MeasureTheory.Measure.exists_isHaarMeasure_map_continuousMulEquiv_eq_prod μN μN₂ (splitNHomeo v)
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

  let d : GL (Fin 2) (v.adicCompletion ℚ) → ℝ≥0∞ :=
    HaarQuotient.density ((unipotentGL2Hom (R := v.adicCompletion ℚ)).range) μN₂
  let D' : ↥(awayFrom v) → ℝ≥0∞ := HaarQuotient.density (RSCarrier.finUnipotent.subgroupOf (awayFrom v)) μN'
  let Dx : ↥(finiteAdelicGL2Subgroup ℚ) → ℝ≥0∞ := fun g => d (projAt v g) * D' ((splitAtHomeo v).symm g).2
  have hd : Measurable d := measurable_density _ _
  have hD' : Measurable D' := measurable_density _ _
  have hDx : Measurable Dx :=
    (hd.comp (continuous_projAt v).measurable).mul
      (hD'.comp (continuous_snd.comp (splitAtHomeo v).symm.continuous).measurable)
  have hadm : ∀ g : finiteAdelicGL2Subgroup ℚ,
      ∫⁻ n : ↥(RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)), Dx ((n : finiteAdelicGL2Subgroup ℚ) * g) ∂μN = 1 := by
    intro g
    let Fg : ↥((unipotentGL2Hom (R := v.adicCompletion ℚ)).range) × ↥(RSCarrier.finUnipotent.subgroupOf (awayFrom v)) → ℝ≥0∞ :=
      fun q => d ((q.1 : GL (Fin 2) (v.adicCompletion ℚ)) * projAt v g) * D' ((q.2 : ↥(awayFrom v)) * ((splitAtHomeo v).symm g).2)
    have hpt : (fun n : ↥(RSCarrier.finUnipotent : Subgroup ↥(finiteAdelicGL2Subgroup ℚ)) => Dx ((n : finiteAdelicGL2Subgroup ℚ) * g)) =
        fun n => Fg (splitNHomeo v n) := by
      funext n
      show d (projAt v ((n : finiteAdelicGL2Subgroup ℚ) * g)) * D' ((splitAtHomeo v).symm ((n : finiteAdelicGL2Subgroup ℚ) * g)).2 =
        d (projAt v (n : finiteAdelicGL2Subgroup ℚ) * projAt v g) *
          D' (((splitAt v).symm (n : finiteAdelicGL2Subgroup ℚ)).2 * ((splitAtHomeo v).symm g).2)
      rw [map_mul, map_mul, Prod.snd_mul]
      rfl
    rw [hpt]
    let eN := (splitNHomeo v).toHomeomorph.toMeasurableEquiv
    have h1 : ∫⁻ n, Fg (splitNHomeo v n) ∂μN = ∫⁻ q, Fg q ∂(Measure.map (splitNHomeo v) μN) := by
      rw [show (⇑(splitNHomeo v) : _ → _) = ⇑eN from rfl, lintegral_map_equiv]
    have hf : AEMeasurable (fun x : ↥((unipotentGL2Hom (R := v.adicCompletion ℚ)).range) =>
        d ((x : GL (Fin 2) (v.adicCompletion ℚ)) * projAt v g)) μN₂ :=
      (hd.comp (continuous_subtype_val.mul continuous_const).measurable).aemeasurable
    have hg : AEMeasurable (fun m : ↥(RSCarrier.finUnipotent.subgroupOf (awayFrom v)) =>
        D' ((m : ↥(awayFrom v)) * ((splitAtHomeo v).symm g).2)) μN' :=
      (hD'.comp (continuous_subtype_val.mul continuous_const).measurable).aemeasurable
    rw [h1, hNsplit, show ∫⁻ q, Fg q ∂(μN₂.prod μN') = _ from lintegral_prod_mul hf hg,
      HaarQuotient.lintegral_density_mul_eq_one _ (isClosed_localUnipotent v) μN₂ (projAt v g),
      HaarQuotient.lintegral_density_mul_eq_one _ (isClosed_finUnipotent_subgroupOf_awayFrom v) μN' _, one_mul]

  let Θ := (splitAtHomeo v).toHomeomorph.toMeasurableEquiv
  have hμ : Measure.map Θ (μ₂.prod μ') = μ := by
    rw [← hsplit]
    exact MeasurableEquiv.map_map_symm Θ
  have hDxΘ : Dx ∘ Θ = fun q => d q.1 * D' q.2 := by
    funext q
    show d (projAt v (splitAt v q)) * D' ((splitAtHomeo v).symm (splitAtHomeo v q)).2 = d q.1 * D' q.2
    rw [(splitAtHomeo v).symm_apply_apply]
    congr 2
    show ((splitAt v).symm (splitAt v q)).1 = q.1
    rw [MulEquiv.symm_apply_apply]

  refine ⟨Measure.map ((↑) : ↥(awayFrom v) → ↥(finiteAdelicGL2Subgroup ℚ)) (μ'.withDensity D'), inferInstance, ?_, ?_⟩
  · have hmeas : MeasurableSet {g' : ↥(finiteAdelicGL2Subgroup ℚ) | localAt ℚ v (g' : AdelicGL2 (𝓞 ℚ) ℚ) = 1} :=
      (isClosed_awayFrom v).measurableSet
    rw [ae_map_iff measurable_subtype_coe.aemeasurable hmeas]
    exact ae_of_all _ fun k => k.2
  · intro Φ hΦ hinv
    have hstep1 : ∫⁻ g, Φ g ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) =
        ∫⁻ g, Φ g ∂(μ.withDensity Dx) :=
      lintegral_withDensity_eq_of_admissible μ RSCarrier.finUnipotent isClosed_finUnipotent μN Dx hDx hadm Φ hΦ hinv
    have hF2 : Measurable fun q : ↥(finiteAdelicGL2Subgroup ℚ) × GL (Fin 2) (v.adicCompletion ℚ) =>
        Φ (q.1 * RSCarrier.finFactor (placeEmbed ℚ v q.2)) := by
      have : (fun q : ↥(finiteAdelicGL2Subgroup ℚ) × GL (Fin 2) (v.adicCompletion ℚ) =>
          q.1 * RSCarrier.finFactor (placeEmbed ℚ v q.2)) = fun q => q.1 * embAt v q.2 := by
        funext q; rw [finFactor_placeEmbed]
      refine hΦ.comp ?_
      rw [this]
      exact (continuous_fst.mul ((continuous_embAt v).comp continuous_snd)).measurable
    have hFm : Measurable fun g' : ↥(finiteAdelicGL2Subgroup ℚ) =>
        ∫⁻ x, Φ (g' * RSCarrier.finFactor (placeEmbed ℚ v x))
          ∂(μ₂.withDensity (HaarQuotient.density (unipotentGL2Hom (R := v.adicCompletion ℚ)).range μN₂)) :=
      hF2.lintegral_prod_right'
    rw [hstep1, ← hμ, withDensity_map_equiv Θ _ Dx, lintegral_map_equiv, hDxΘ, ← prod_withDensity hd hD',
      lintegral_map hFm measurable_subtype_coe]
    refine (lintegral_prod_symm (μ := μ₂.withDensity d) (ν := μ'.withDensity D') (fun a => Φ (Θ a))
      (hΦ.comp Θ.measurable).aemeasurable).trans ?_
    refine lintegral_congr fun k => lintegral_congr fun x => ?_
    show Φ (splitAtHomeo v (x, k)) = Φ ((k : ↥(finiteAdelicGL2Subgroup ℚ)) * RSCarrier.finFactor (placeEmbed ℚ v x))
    rw [splitAtHomeo_apply, splitAt_apply, embAt_mul_comm, finFactor_placeEmbed]

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_sFinite_forall_lintegral_withDensity_density_eq_lintegral_lintegral_mul_finFactor_placeEmbed (solution)
