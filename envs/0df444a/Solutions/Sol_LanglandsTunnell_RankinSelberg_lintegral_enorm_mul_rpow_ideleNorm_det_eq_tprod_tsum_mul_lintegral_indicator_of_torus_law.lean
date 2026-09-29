-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.lintegral_enorm_mul_rpow_ideleNorm_det_eq_tprod_tsum_mul_lintegral_indicator_of_torus_law
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d5a9d30a-4623-590c-8cc1-bd1bff4cce34

import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_LanglandsTunnell_RankinSelberg_lintegral_enorm_mul_rpow_ideleNorm_det_eq_tsum_mul_lintegral_indicator_of_torus_law_at
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_lintegral_enorm_mul_rpow_ideleNorm_det_eq_tprod_tsum_mul_lintegral_indicator_of_torus_law
p2m_attr_erase "instance" "FixedPoints.instMulActionElemFixedPointsOfSMulCommClass_definitions FixedPoints.module FixedPoints.instSMulElemFixedPointsOfSMulCommClass_definitions FixedPoints.instAddCommMonoidElemFixedPoints_definitions instCountableOfNumberField_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "AutomorphicForm.rightTranslationEmbed_smul_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one FixedPoints.coe_zero FixedPoints.coe_smul FixedPoints.coe_add AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel

open MeasureTheory NumberField AutomorphicForm IsDedekindDomain UnramifiedWhittaker AdelicDock Topology
open scoped ENNReal

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RankinSelberg.lintegral_enorm_mul_rpow_ideleNorm_det_eq_tsum_mul_lintegral_indicator_of_torus_law_at"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "lintegral_enorm_mul_rpow_ideleNorm_det_eq_tsum_mul_lintegral_indicator_of_torus_law_at"
namespace LintPeel
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

section LevelOneOpen

namespace IntegralUnits

open Matrix NumberField

variable {F : Type*} [Field F] (O : ValuationSubring F)

def IsIntegralUnit (k : GL (Fin 2) F) : Prop :=
  (∀ i j, (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O) ∧ ∀ i j, ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O

variable {O}

theorem isOpen_setOf_isIntegralUnit [TopologicalSpace F] [IsTopologicalRing F] (hO : IsOpen (O : Set F)) :
    IsOpen {k : GL (Fin 2) F | IsIntegralUnit O k} := by
  have h1 : ∀ i j : Fin 2, IsOpen {k : GL (Fin 2) F | (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O} := fun i j =>
    hO.preimage (Units.continuous_val.matrix_elem i j)
  have h2 : ∀ i j : Fin 2, IsOpen {k : GL (Fin 2) F | ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O} :=
    fun i j => hO.preimage (Units.continuous_coe_inv.matrix_elem i j)
  have hset : {k : GL (Fin 2) F | IsIntegralUnit O k} =
      (⋂ i, ⋂ j, {k : GL (Fin 2) F | (k : Matrix (Fin 2) (Fin 2) F) i j ∈ O}) ∩
        ⋂ i, ⋂ j, {k : GL (Fin 2) F | ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ O} := by
    ext k
    simp only [IsIntegralUnit, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h1 i j).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h2 i j)

end IntegralUnits

namespace LevelOne

open IsDedekindDomain AdelicDock IntegralUnits

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem isLocalLevelOne_top_iff (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) :
    IsLocalLevelOne (𝓞 ℚ) ℚ v ⊤ m ↔ ∀ i j, m i j ∈ v.adicCompletionIntegers ℚ := by
  refine ⟨fun h => h.integral, fun h => ⟨h, ?_, ?_⟩⟩
  · rw [AdelicLevel.idealBound_top]
    have := h 1 0
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this
  · rw [AdelicLevel.idealBound_top]
    have := sub_mem (h 1 1) (one_mem (v.adicCompletionIntegers ℚ))
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this

theorem mem_localLevelOne_top_iff (k : GL (Fin 2) (v.adicCompletion ℚ)) :
    k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤ ↔ IsIntegralUnit (v.adicCompletionIntegers ℚ) k := by
  rw [mem_localLevelOne_iff, isLocalLevelOne_top_iff, isLocalLevelOne_top_iff]
  exact Iff.rfl

theorem isOpen_localLevelOne_top :
    IsOpen ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) := by
  have hset : ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ : Subgroup (GL (Fin 2) (v.adicCompletion ℚ))) :
      Set (GL (Fin 2) (v.adicCompletion ℚ))) =
        {k : GL (Fin 2) (v.adicCompletion ℚ) | IsIntegralUnit (v.adicCompletionIntegers ℚ) k} := by
    ext k
    exact mem_localLevelOne_top_iff v k
  rw [hset]
  exact isOpen_setOf_isIntegralUnit ((AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 ℚ) ℚ).out v)

end LevelOne

end LevelOneOpen

section Places

theorem localAt_unipotentGL2Hom (q : HeightOneSpectrum (𝓞 ℚ)) (y : Multiplicative (AdeleRing (𝓞 ℚ) ℚ)) :
    localAt ℚ q (AutomorphicForm.unipotentGL2Hom y) =
      AutomorphicForm.unipotentGL2Hom (Multiplicative.ofAdd ((Multiplicative.toAdd y).2 q)) := by
  apply Units.ext
  ext i j
  simp only [localAt, MonoidHom.coe_comp, Function.comp_apply, AdelicLevel.finComponent_apply,
    AdelicLevel.glFin_apply, AutomorphicForm.unipotentGL2Hom, MonoidHom.coe_mk, OneHom.coe_mk,
    AutomorphicForm.unipotentGL2_coe, toAdd_ofAdd]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

theorem localAt_mem_range_of_mem_finUnipotent (q : HeightOneSpectrum (𝓞 ℚ)) (n : RSCarrier.finUnipotent) :
    localAt ℚ q ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) ∈
      (AutomorphicForm.unipotentGL2Hom (R := q.adicCompletion ℚ)).range := by
  obtain ⟨y, hy⟩ : ((n : finiteAdelicGL2Subgroup ℚ) : AdelicGL2 (𝓞 ℚ) ℚ) ∈
      (AutomorphicForm.unipotentGL2Hom (R := AdeleRing (𝓞 ℚ) ℚ)).range := Subgroup.mem_subgroupOf.mp n.2
  rw [← hy, localAt_unipotentGL2Hom]
  exact ⟨_, rfl⟩

def localCell (q : HeightOneSpectrum (𝓞 ℚ)) : Set (GL (Fin 2) (q.adicCompletion ℚ)) :=
  {y | ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := q.adicCompletion ℚ)).range,
    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q ⊤, y = n * k}

theorem isOpen_localCell (q : HeightOneSpectrum (𝓞 ℚ)) : IsOpen (localCell q) := by
  have hset : localCell q =
      ⋃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := q.adicCompletion ℚ)).range,
        (fun k => n * k) '' ((AdelicDock.localLevelOne (𝓞 ℚ) ℚ q ⊤ : Subgroup (GL (Fin 2) (q.adicCompletion ℚ))) :
          Set (GL (Fin 2) (q.adicCompletion ℚ))) := by
    ext y
    simp only [localCell, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨n, hn, k, hk, rfl⟩
      exact ⟨n, hn, k, hk, rfl⟩
    · rintro ⟨n, hn, k, hk, rfl⟩
      exact ⟨n, hn, k, hk, rfl⟩
  rw [hset]
  exact isOpen_biUnion fun n _ => (isOpenMap_mul_left n) _ (LevelOne.isOpen_localLevelOne_top q)

theorem mem_localCell_unipotent_mul_iff (v : HeightOneSpectrum (𝓞 ℚ)) {n : GL (Fin 2) (v.adicCompletion ℚ)}
    (hn : n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    n * x ∈ localCell v ↔ x ∈ localCell v := by
  constructor
  · rintro ⟨n', hn', k, hk, h⟩
    refine ⟨n⁻¹ * n', mul_mem (inv_mem hn) hn', k, hk, ?_⟩
    rw [mul_assoc, ← h, inv_mul_cancel_left]
  · rintro ⟨n', hn', k, hk, h⟩
    exact ⟨n * n', mul_mem hn hn', k, hk, by rw [h, mul_assoc]⟩

theorem localAt_placeEmbed_of_ne (w v : HeightOneSpectrum (𝓞 ℚ)) (x : GL (Fin 2) (v.adicCompletion ℚ))
    (hw : w ≠ v) : localAt ℚ w (placeEmbed ℚ v x) = 1 := by
  show AdelicLevel.finComponent (𝓞 ℚ) ℚ w
    (AdelicLevel.glFin (𝓞 ℚ) ℚ (finEmbed (𝓞 ℚ) ℚ (localEmbed (𝓞 ℚ) ℚ v x))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 ℚ) ℚ v x hw]

end Places

section Cells

local instance : BorelSpace (AdelicGL2 (𝓞 ℚ) ℚ) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ

def preCell (v : HeightOneSpectrum (𝓞 ℚ)) : Set (finiteAdelicGL2Subgroup ℚ) :=
  {g | ∃ n ∈ (unipotentGL2Hom (R := v.adicCompletion ℚ)).range, ∃ k ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤,
    localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}

def cellA (v : HeightOneSpectrum (𝓞 ℚ)) : Set (AdelicGL2 (𝓞 ℚ) ℚ) :=
  {a | ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v a = n * k}

theorem mem_preCell_iff (v : HeightOneSpectrum (𝓞 ℚ)) (g : finiteAdelicGL2Subgroup ℚ) :
    g ∈ preCell v ↔ localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ localCell v :=
  Iff.rfl

theorem mem_preCell_unipotent_mul_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : RSCarrier.finUnipotent)
    (g : finiteAdelicGL2Subgroup ℚ) : (n : finiteAdelicGL2Subgroup ℚ) * g ∈ preCell v ↔ g ∈ preCell v := by
  rw [mem_preCell_iff, mem_preCell_iff, Subgroup.coe_mul, map_mul]
  exact mem_localCell_unipotent_mul_iff v (localAt_mem_range_of_mem_finUnipotent v n) _

theorem measurableSet_preCell (v : HeightOneSpectrum (𝓞 ℚ)) : MeasurableSet (preCell v) := by
  have hopen : IsOpen (localCell v) := isOpen_localCell v
  exact (hopen.preimage ((continuous_localAt (K := ℚ) (v := v)).comp continuous_subtype_val)).measurableSet

theorem finite_setOf_not_mem_preCell (g : finiteAdelicGL2Subgroup ℚ) :
    {v : HeightOneSpectrum (𝓞 ℚ) | g ∉ preCell v}.Finite := by
  have hent : ∀ (a : AdelicGL2 (𝓞 ℚ) ℚ) (i j : Fin 2), ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      ((localAt ℚ v a : GL (Fin 2) (v.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) i j ∈
        v.adicCompletionIntegers ℚ := by
    intro a i j
    have h := (((a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 : FiniteAdeleRing (𝓞 ℚ) ℚ).eventually
    refine h.mono fun w hw => ?_
    simp only [localAt, MonoidHom.coe_comp, Function.comp_apply, AdelicLevel.finComponent_apply,
      AdelicLevel.glFin_apply]
    exact hw
  have hK : ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ localLevelOne (𝓞 ℚ) ℚ v ⊤ := by
    have h1 := Filter.eventually_all.2 fun i : Fin 2 => Filter.eventually_all.2 fun j : Fin 2 =>
      hent (g : AdelicGL2 (𝓞 ℚ) ℚ) i j
    have h2 := Filter.eventually_all.2 fun i : Fin 2 => Filter.eventually_all.2 fun j : Fin 2 =>
      hent ((g : AdelicGL2 (𝓞 ℚ) ℚ)⁻¹) i j
    filter_upwards [h1, h2] with v hv1 hv2
    rw [LevelOne.mem_localLevelOne_top_iff]
    refine ⟨hv1, fun i j => ?_⟩
    rw [← map_inv]
    exact hv2 i j
  refine (Filter.eventually_cofinite.1 hK).subset fun v hv => ?_
  intro hv'
  exact hv ⟨1, one_mem _, _, hv', by rw [one_mul]⟩

variable {ι : Type*} (pl : ι → HeightOneSpectrum (𝓞 ℚ))

def cocellsA (T : Finset ι) : Set (AdelicGL2 (𝓞 ℚ) ℚ) := {a | ∀ i, i ∉ T → a ∈ cellA (pl i)}

def cocells (T : Finset ι) : Set (finiteAdelicGL2Subgroup ℚ) := {g | ∀ i, i ∉ T → g ∈ preCell (pl i)}

theorem mem_cocellsA_coe (T : Finset ι) (g : finiteAdelicGL2Subgroup ℚ) :
    (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ cocellsA pl T ↔ g ∈ cocells pl T := Iff.rfl

theorem measurableSet_cocells [Countable ι] (T : Finset ι) : MeasurableSet (cocells pl T) := by
  have h : cocells pl T = ⋂ i : ι, ⋂ (_ : i ∉ T), preCell (pl i) := by
    ext g
    simp only [cocells, Set.mem_setOf_eq, Set.mem_iInter]
  rw [h]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurableSet_preCell (pl i)

theorem cocells_mono {T T' : Finset ι} (h : T ⊆ T') : cocells pl T ⊆ cocells pl T' :=
  fun _ hg i hi => hg i (fun h' => hi (h h'))

theorem mul_placeEmbed_mem_cocellsA_iff (T : Finset ι) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ∀ i, i ∉ T → pl i ≠ v) (a : AdelicGL2 (𝓞 ℚ) ℚ) (x : GL (Fin 2) (v.adicCompletion ℚ)) :
    a * placeEmbed ℚ v x ∈ cocellsA pl T ↔ a ∈ cocellsA pl T := by
  simp only [cocellsA, cellA, Set.mem_setOf_eq]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [map_mul, localAt_placeEmbed_of_ne (pl i) v x (hv i hi), mul_one]

theorem unipotent_mul_mem_cocells_iff (T : Finset ι) (n : RSCarrier.finUnipotent)
    (g : finiteAdelicGL2Subgroup ℚ) :
    (n : finiteAdelicGL2Subgroup ℚ) * g ∈ cocells pl T ↔ g ∈ cocells pl T := by
  simp only [cocells, Set.mem_setOf_eq]
  exact forall_congr' fun i => forall_congr' fun _ => mem_preCell_unipotent_mul_iff (pl i) n g

theorem indicator_preCell_indicator_cocellsA [DecidableEq ι] (T : Finset ι) (i₀ : ι) (hi₀ : i₀ ∉ T)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : finiteAdelicGL2Subgroup ℚ) :
    (preCell (pl i₀)).indicator
        (fun g : finiteAdelicGL2Subgroup ℚ => (cocellsA pl (insert i₀ T)).indicator W g) g =
      (cocellsA pl T).indicator W g := by
  have hiff : g ∈ preCell (pl i₀) ∧ (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ cocellsA pl (insert i₀ T) ↔
      (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ cocellsA pl T := by
    simp only [mem_cocellsA_coe, cocells, Set.mem_setOf_eq, Finset.mem_insert, not_or]
    constructor
    · rintro ⟨h0, h⟩ i hi
      by_cases hii : i = i₀
      · subst hii; exact h0
      · exact h i ⟨hii, hi⟩
    · intro h
      exact ⟨h i₀ hi₀, fun i hi => h i hi.2⟩
  by_cases h : (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ cocellsA pl T
  · obtain ⟨h0, h1⟩ := hiff.mpr h
    rw [Set.indicator_of_mem h0, Set.indicator_of_mem h1, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h]
    by_cases h0 : g ∈ preCell (pl i₀)
    · rw [Set.indicator_of_mem h0, Set.indicator_of_notMem (fun h1 => h (hiff.mp ⟨h0, h1⟩))]
    · rw [Set.indicator_of_notMem h0]

end Cells

theorem countable_heightOneSpectrum (K : Type) [Field K] [NumberField K] :
    Countable (HeightOneSpectrum (𝓞 K)) := by
  have hI : Set.Countable (Set.univ : Set (Ideal (𝓞 K))) := by
    have : (Set.univ : Set (Ideal (𝓞 K))) = ⋃ n : ℕ, {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := by
      ext I; simp
    rw [this]
    exact Set.countable_iUnion (fun n => (Ideal.finite_setOf_absNorm_eq n).countable)
  haveI : Countable (Ideal (𝓞 K)) := Set.countable_univ_iff.mp hI
  exact (Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
    (fun v w h => HeightOneSpectrum.ext h))

theorem hasProd_iSup_of_one_le {ι : Type*} (A : ι → ℝ≥0∞) (hA : ∀ i, 1 ≤ A i) :
    HasProd A (⨆ T : Finset ι, ∏ i ∈ T, A i) := by
  have hmono : Monotone (fun T : Finset ι => ∏ i ∈ T, A i) :=
    fun T T' h => Finset.prod_le_prod_of_subset_of_one_le' h (fun i _ _ => hA i)
  unfold HasProd
  simpa using tendsto_atTop_iSup hmono

end LanglandsTunnell.RankinSelberg.LintPeel

end

open _root_.LanglandsTunnell.RankinSelberg _root_.P2MW.S_LanglandsTunnell_RankinSelberg_lintegral_enorm_mul_rpow_ideleNorm_det_eq_tprod_tsum_mul_lintegral_indicator_of_torus_law.LanglandsTunnell.RankinSelberg LanglandsTunnell.RankinSelberg.LintPeel in

theorem solution
    (μ : Measure (finiteAdelicGL2Subgroup ℚ)) [μ.IsHaarMeasure]
    (μN : Measure (RSCarrier.finUnipotent)) [μN.IsHaarMeasure]
    [SecondCountableTopology (finiteAdelicGL2Subgroup ℚ)]
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (lam om lam' om' : HeightOneSpectrum (𝓞 ℚ) → ℂ) (κ : ℝ)
    (hbd : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ‖lam v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖lam' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖om' v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
    (W F : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hinv : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
      W ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
          F ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
        W (g : AdelicGL2 (𝓞 ℚ) ℚ) * F (g : AdelicGL2 (𝓞 ℚ) ℚ))
    (hN : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
      (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
      (∃ r : v.adicCompletionIntegers ℚ,
        ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
          algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
      ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), W (placeEmbed ℚ v (unipotent x) * g) = ψ x * W g)
    (hWK : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → W (g * placeEmbed ℚ v x) = W g)
    (hFK : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → F (g * placeEmbed ℚ v x) = F g)
    (hT : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∀ hv : v ∉ S, ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v g = 1 →
      W (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n)) *
        F (g * placeEmbed ℚ v
            (diagZ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) m *
              scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπ v hv) ^ n)) =
        (if 0 ≤ m ∧ 0 ≤ n then
          (om v * om' v) ^ n.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam v) (om v) m.toNat *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lam' v) (om' v) m.toNat
         else 0) * (W g * F g))
    (hm : Measurable fun g : finiteAdelicGL2Subgroup ℚ => W g * F g)
    (τ : ℝ) :
    ∫⁻ g : finiteAdelicGL2Subgroup ℚ,
        ‖W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ)
        ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) =
      (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
          ∑' p : ℤ × ℤ,
            ENNReal.ofReal
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (p.1 - p.2) *
                ‖(if 0 ≤ p.1 - p.2 ∧ 0 ≤ p.2 then
                    (om v.1 * om' v.1) ^ p.2.toNat *
                      heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam v.1) (om v.1) (p.1 - p.2).toNat *
                      heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam' v.1) (om' v.1) (p.1 - p.2).toNat
                  else 0)‖ *
                (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(p.1 + p.2))) ^ τ)) *
        ∫⁻ g : finiteAdelicGL2Subgroup ℚ,
          ‖{g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                  ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => W g) g *
              {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
                  ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
                    ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
                      localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => F g) g‖ₑ *
            ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ)
          ∂(μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN)) := by
  classical
  haveI : Countable (HeightOneSpectrum (𝓞 ℚ)) := countable_heightOneSpectrum ℚ
  haveI : BorelSpace (AdelicGL2 (𝓞 ℚ) ℚ) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  set ν := μ.withDensity (HaarQuotient.density RSCarrier.finUnipotent μN) with hν

  set A : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} → ℝ≥0∞ := fun v => (∑' p : ℤ × ℤ,
            ENNReal.ofReal
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (p.1 - p.2) *
                ‖(if 0 ≤ p.1 - p.2 ∧ 0 ≤ p.2 then
                    (om v.1 * om' v.1) ^ p.2.toNat *
                      heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam v.1) (om v.1) (p.1 - p.2).toNat *
                      heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam' v.1) (om' v.1) (p.1 - p.2).toNat
                  else 0)‖ *
                (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(p.1 + p.2))) ^ τ)) with hA

  have hwm : Measurable fun g : finiteAdelicGL2Subgroup ℚ => ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ) := by
    have hc : Continuous fun g : finiteAdelicGL2Subgroup ℚ =>
        TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) :=
      (TateGlobal.continuous_ideleNorm_det ℚ).comp continuous_subtype_val
    exact ENNReal.measurable_ofReal.comp
      (hc.rpow_const fun g => Or.inl (TateGlobal.ideleNorm_pos _).ne').measurable

  have hmcut : ∀ T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
      Measurable fun g : finiteAdelicGL2Subgroup ℚ => (cocellsA Subtype.val T).indicator W g * F g := by
    intro T
    have h : (fun g : finiteAdelicGL2Subgroup ℚ => (cocellsA Subtype.val T).indicator W g * F g) =
        (cocells Subtype.val T).indicator (fun g : finiteAdelicGL2Subgroup ℚ => W g * F g) := by
      funext g
      simp only [Set.indicator_apply, mem_cocellsA_coe]
      split_ifs <;> simp
    rw [h]
    exact hm.indicator (measurableSet_cocells Subtype.val T)

  have key : ∀ T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S},
      (∫⁻ g, ‖(cocellsA Subtype.val T).indicator W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ) ∂ν) = (∏ v ∈ T, A v) * (∫⁻ g, ‖(cocellsA Subtype.val (∅ : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S})).indicator W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ) ∂ν) := by
    intro T
    induction T using Finset.induction_on with
    | empty => rw [Finset.prod_empty, one_mul]
    | insert v T hvT ih =>
      have hne : ∀ i : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, i ∉ insert v T → (Subtype.val i) ≠ v.1 :=
        fun i hi h => hi (by rw [Subtype.ext h]; exact Finset.mem_insert_self v T)
      have hmemE : ∀ (a : AdelicGL2 (𝓞 ℚ) ℚ) (x : GL (Fin 2) (v.1.adicCompletion ℚ)),
          a * placeEmbed ℚ v.1 x ∈ cocellsA Subtype.val (insert v T) ↔ a ∈ cocellsA Subtype.val (insert v T) :=
        fun a x => mul_placeEmbed_mem_cocellsA_iff Subtype.val (insert v T) hne a x
      have hinvT : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ),
          (cocellsA Subtype.val (insert v T)).indicator W
              ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) *
            F ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
          (cocellsA Subtype.val (insert v T)).indicator W (g : AdelicGL2 (𝓞 ℚ) ℚ) * F (g : AdelicGL2 (𝓞 ℚ) ℚ) := by
        intro n g
        have hmm : ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) ∈
            cocellsA Subtype.val (insert v T) ↔ (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ cocellsA Subtype.val (insert v T) := by
          rw [mem_cocellsA_coe, mem_cocellsA_coe]
          exact unipotent_mul_mem_cocells_iff Subtype.val (insert v T) n g
        simp only [Set.indicator_apply, hmm]
        split_ifs with h
        · exact hinv n g
        · simp
      have hWKT : ∀ (x : GL (Fin 2) (v.1.adicCompletion ℚ)) (a : AdelicGL2 (𝓞 ℚ) ℚ),
          x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v.1 ⊤ →
            (cocellsA Subtype.val (insert v T)).indicator W (a * placeEmbed ℚ v.1 x) =
              (cocellsA Subtype.val (insert v T)).indicator W a := by
        intro x a hx
        simp only [Set.indicator_apply, hmemE a x, hWK v.1 v.2 x a hx]
      have hTT : ∀ (a : AdelicGL2 (𝓞 ℚ) ℚ) (m n : ℤ), localAt ℚ v.1 a = 1 →
          (cocellsA Subtype.val (insert v T)).indicator W (a * placeEmbed ℚ v.1
                (diagZ (algebraMap (v.1.adicCompletionIntegers ℚ) (v.1.adicCompletion ℚ) (ϖ v.1)) (hπ v.1 v.2) m *
                  scalarPi (algebraMap (v.1.adicCompletionIntegers ℚ) (v.1.adicCompletion ℚ) (ϖ v.1)) (hπ v.1 v.2) ^ n)) *
            F (a * placeEmbed ℚ v.1
                (diagZ (algebraMap (v.1.adicCompletionIntegers ℚ) (v.1.adicCompletion ℚ) (ϖ v.1)) (hπ v.1 v.2) m *
                  scalarPi (algebraMap (v.1.adicCompletionIntegers ℚ) (v.1.adicCompletion ℚ) (ϖ v.1)) (hπ v.1 v.2) ^ n)) =
          (if 0 ≤ m ∧ 0 ≤ n then
            (om v.1 * om' v.1) ^ n.toNat *
              heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam v.1) (om v.1) m.toNat *
              heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam' v.1) (om' v.1) m.toNat
           else 0) *
            ((cocellsA Subtype.val (insert v T)).indicator W a * F a) := by
        intro a m n ha
        have hm' := hmemE a
          (diagZ (algebraMap (v.1.adicCompletionIntegers ℚ) (v.1.adicCompletion ℚ) (ϖ v.1)) (hπ v.1 v.2) m *
                  scalarPi (algebraMap (v.1.adicCompletionIntegers ℚ) (v.1.adicCompletion ℚ) (ϖ v.1)) (hπ v.1 v.2) ^ n)
        by_cases h : a ∈ cocellsA Subtype.val (insert v T)
        · have h' := hm'.mpr h
          simp only [Set.indicator_apply, if_pos h, if_pos h']
          exact hT v.1 v.2 a m n ha
        · have h' := fun hh => h (hm'.mp hh)
          simp only [Set.indicator_apply, if_neg h, if_neg h', zero_mul, mul_zero]
      have step :=
        LanglandsTunnell.RankinSelberg.lintegral_enorm_mul_rpow_ideleNorm_det_eq_tsum_mul_lintegral_indicator_of_torus_law_at
          μ μN v.1 (hπ v.1 v.2) (hϖ v.1 v.2)
          (fun m n => (if 0 ≤ m ∧ 0 ≤ n then
            (om v.1 * om' v.1) ^ n.toNat *
              heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam v.1) (om v.1) m.toNat *
              heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam' v.1) (om' v.1) m.toNat
           else 0))
          ((cocellsA Subtype.val (insert v T)).indicator W) F hinvT hWKT (hFK v.1 v.2) hTT (hmcut (insert v T)) τ

      have hcut : ∀ g : finiteAdelicGL2Subgroup ℚ,
          ‖(preCell v.1).indicator
                (fun g : finiteAdelicGL2Subgroup ℚ => (cocellsA Subtype.val (insert v T)).indicator W g) g *
              (preCell v.1).indicator (fun g : finiteAdelicGL2Subgroup ℚ => F g) g‖ₑ =
            ‖(cocellsA Subtype.val T).indicator W g * F g‖ₑ := by
        intro g
        rw [indicator_preCell_indicator_cocellsA Subtype.val T v hvT W g]
        by_cases hg : g ∈ preCell v.1
        · rw [Set.indicator_of_mem hg]
        · have h0 : (g : AdelicGL2 (𝓞 ℚ) ℚ) ∉ cocellsA Subtype.val T :=
            fun h => hg ((mem_cocellsA_coe Subtype.val T g).mp h v hvT)
          rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem h0, zero_mul, zero_mul]
      have hR : (∫⁻ g, ‖(preCell v.1).indicator
                (fun g : finiteAdelicGL2Subgroup ℚ => (cocellsA Subtype.val (insert v T)).indicator W g) g *
              (preCell v.1).indicator (fun g : finiteAdelicGL2Subgroup ℚ => F g) g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ) ∂ν) =
          (∫⁻ g, ‖(cocellsA Subtype.val T).indicator W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ) ∂ν) := by
        refine lintegral_congr fun g => ?_
        rw [hcut g]
      rw [Finset.prod_insert hvT, mul_assoc, ← ih, ← hR]
      simpa only [hA, hν, preCell] using step

  have hbase : (∫⁻ g, ‖(cocellsA Subtype.val (∅ : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S})).indicator W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ) ∂ν) =
      ∫⁻ g, ‖{g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
            localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => W g) g *
              {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
            localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k}.indicator (fun g => F g) g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ) ∂ν := by
    refine lintegral_congr fun g => ?_
    have hC : g ∈ {g : finiteAdelicGL2Subgroup ℚ | ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
          ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤,
            localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n * k} ↔ (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ cocellsA Subtype.val (∅ : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}) := by
      simp only [Set.mem_setOf_eq, cocellsA, cellA, Finset.notMem_empty, not_false_eq_true, forall_const]
      exact ⟨fun h i => h i.1 i.2, fun h w hw => h ⟨w, hw⟩⟩
    by_cases hg : (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ cocellsA Subtype.val (∅ : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S})
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hC.mpr hg), Set.indicator_of_mem (hC.mpr hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hC.mp h)), zero_mul, zero_mul]

  have hsup : (∫⁻ g, ‖W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ) ∂ν) =
      ⨆ T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, (∫⁻ g, ‖(cocellsA Subtype.val T).indicator W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ) ∂ν) := by
    have hpt : ∀ g : finiteAdelicGL2Subgroup ℚ,
        (⨆ T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, ‖(cocellsA Subtype.val T).indicator W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ)) =
          ‖W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ) := by
      intro g
      obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ cocellsA Subtype.val T₀ := by
        refine ⟨(finite_setOf_not_mem_preCell g).toFinset.subtype (fun v => v ∉ S), ?_⟩
        rw [mem_cocellsA_coe]
        intro i hi
        by_contra hgi
        exact hi (Finset.mem_subtype.mpr ((Set.Finite.mem_toFinset _).mpr hgi))
      apply le_antisymm
      · refine iSup_le fun T => ?_
        by_cases h : (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ cocellsA Subtype.val T
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h, zero_mul, enorm_zero, zero_mul]
          exact zero_le
      · refine le_iSup_of_le T₀ ?_
        rw [Set.indicator_of_mem hT₀]
    have hmeas : ∀ T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, Measurable fun g : finiteAdelicGL2Subgroup ℚ =>
        ‖(cocellsA Subtype.val T).indicator W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ) :=
      fun T => (hmcut T).enorm.mul hwm
    have hmono : Monotone fun (T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}) (g : finiteAdelicGL2Subgroup ℚ) =>
        ‖(cocellsA Subtype.val T).indicator W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ) := by
      intro T T' hTT' g
      by_cases h : (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ cocellsA Subtype.val T
      · have h' : (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ cocellsA Subtype.val T' :=
          (mem_cocellsA_coe Subtype.val T' g).mpr (cocells_mono Subtype.val hTT' ((mem_cocellsA_coe Subtype.val T g).mp h))
        simp only [Set.indicator_of_mem h, Set.indicator_of_mem h', le_refl]
      · simp only [Set.indicator_of_notMem h, zero_mul, enorm_zero, zero_le]
    rw [← lintegral_iSup_directed (fun T => (hmeas T).aemeasurable) hmono.directed_le]
    exact lintegral_congr fun g => (hpt g).symm

  have hA1 : ∀ v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, 1 ≤ A v := by
    intro v
    have h0 : ENNReal.ofReal
        (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ ((0 : ℤ × ℤ).1 - (0 : ℤ × ℤ).2) *
          ‖(if 0 ≤ (0 : ℤ × ℤ).1 - (0 : ℤ × ℤ).2 ∧ 0 ≤ (0 : ℤ × ℤ).2 then
              (om v.1 * om' v.1) ^ (0 : ℤ × ℤ).2.toNat *
                heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam v.1) (om v.1)
                  ((0 : ℤ × ℤ).1 - (0 : ℤ × ℤ).2).toNat *
                heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam' v.1) (om' v.1)
                  ((0 : ℤ × ℤ).1 - (0 : ℤ × ℤ).2).toNat
            else 0)‖ *
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-((0 : ℤ × ℤ).1 + (0 : ℤ × ℤ).2))) ^ τ) = 1 := by
      simp [heckeRecursionSeq]
    rw [hA, ← h0]
    exact ENNReal.le_tsum (0 : ℤ × ℤ)
  have hP : HasProd A (⨆ T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, ∏ v ∈ T, A v) := hasProd_iSup_of_one_le A hA1

  have hiSup : (⨆ T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, (∫⁻ g, ‖(cocellsA Subtype.val T).indicator W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ) ∂ν)) =
      (⨆ T : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, ∏ v ∈ T, A v) * (∫⁻ g, ‖(cocellsA Subtype.val (∅ : Finset {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S})).indicator W g * F g‖ₑ * ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) ^ τ) ∂ν) := by
    rw [ENNReal.iSup_mul]
    exact iSup_congr fun T => key T
  rw [show (∏' v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S}, (∑' p : ℤ × ℤ,
            ENNReal.ofReal
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (p.1 - p.2) *
                ‖(if 0 ≤ p.1 - p.2 ∧ 0 ≤ p.2 then
                    (om v.1 * om' v.1) ^ p.2.toNat *
                      heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam v.1) (om v.1) (p.1 - p.2).toNat *
                      heckeRecursionSeq ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) (lam' v.1) (om' v.1) (p.1 - p.2).toNat
                  else 0)‖ *
                (((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(p.1 + p.2))) ^ τ))) = ∏' v, A v from rfl, hP.tprod_eq, hsup, hiSup, hbase]

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_lintegral_enorm_mul_rpow_ideleNorm_det_eq_tprod_tsum_mul_lintegral_indicator_of_torus_law
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_lintegral_enorm_mul_rpow_ideleNorm_det_eq_tprod_tsum_mul_lintegral_indicator_of_torus_law (solution)
