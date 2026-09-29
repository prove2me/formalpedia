-- Prove2me | solution 1 for M4aHerbrand.IdeleGaloisDescent.isClosed_range_prod_unitsAct_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/9b920062-b3b9-5966-8486-e7ce879f7fe8

import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Theorems.Thm_AutomorphicForm_ideleNorm_det_sigmaAdelicAct
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_isClosed_range_prod_unitsAct_pow
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

noncomputable section

namespace R4NC

open NumberField Filter Function Set Topology
open scoped NNReal Pointwise

section Main

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

abbrev II : Type := (AdeleRing (𝓞 L) L)ˣ

abbrev uτ (τ : L ≃ₐ[K] L) : II L →* II L := (D.unitsAct τ).toMonoidHom

abbrev ι : Lˣ →* II L := (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom)

def cN : II L →* II L := ∏ k ∈ Finset.range (orderOf σ), uτ K L D (σ ^ k)

theorem cN_apply (w : II L) : cN K L σ D w = ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) w := by
  unfold cN
  rw [MonoidHom.finsetProd_apply]
  rfl

theorem range_cN_eq :
    Set.range (cN K L σ D) = Set.range (fun w : II L => ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) w) := by
  ext x; simp only [Set.mem_range, cN_apply]

theorem uτ_eq_units_map (τ : L ≃ₐ[K] L) :
    (uτ K L D τ : II L → II L) = Units.map ((D.act τ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) := by
  funext w
  exact Units.ext rfl

theorem continuous_uτ (τ : L ≃ₐ[K] L) : Continuous fun w : II L => D.unitsAct τ w := by
  show Continuous (uτ K L D τ)
  rw [uτ_eq_units_map]
  exact Continuous.units_map _ (D.continuous_act τ)

theorem continuous_cN : Continuous (cN K L σ D) := by
  have : (cN K L σ D : II L → II L) = fun w => ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) w := by
    funext w; exact cN_apply K L σ D w
  rw [this]
  exact continuous_finsetProd _ fun k _ => continuous_uτ K L D (σ ^ k)

def normHom : II L →* ℝ where
  toFun := NumberField.TateGlobal.ideleNorm L
  map_one' := by
    have h := NumberField.TateGlobal.ideleNorm_mul (F := L) 1 1
    rw [one_mul] at h
    have h1 := NumberField.TateGlobal.ideleNorm_pos (F := L) 1
    nlinarith [h, h1]
  map_mul' := NumberField.TateGlobal.ideleNorm_mul

theorem normHom_apply (x : II L) : normHom L x = NumberField.TateGlobal.ideleNorm L x := rfl

theorem sigmaAdelicAct_scalar (τ : L ≃ₐ[K] L) (u : II L) :
    AutomorphicForm.sigmaAdelicAct K L D τ (Matrix.GeneralLinearGroup.scalar (Fin 2) u) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (uτ K L D τ u) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show ((D.act τ : RingAut (AdeleRing (𝓞 L) L)).toRingHom)
      ((Matrix.diagonal fun _ : Fin 2 => (u : AdeleRing (𝓞 L) L)) i j) =
    (Matrix.diagonal fun _ : Fin 2 => ((uτ K L D τ u : II L) : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h, map_zero]

theorem ideleNorm_uτ (τ : L ≃ₐ[K] L) (x : II L) :
    NumberField.TateGlobal.ideleNorm L (uτ K L D τ x) = NumberField.TateGlobal.ideleNorm L x := by
  have h := AutomorphicForm.ideleNorm_det_sigmaAdelicAct K L D τ (Matrix.GeneralLinearGroup.scalar (Fin 2) x)
  rw [sigmaAdelicAct_scalar] at h
  have hdet : ∀ y : II L,
      Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) y) = y * y := by
    intro y
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    show (Matrix.diagonal fun _ : Fin 2 => (y : AdeleRing (𝓞 L) L)).det = _
    rw [Matrix.det_diagonal, Fin.prod_univ_two, Units.val_mul]
  rw [hdet, hdet, NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul] at h
  have h1 := NumberField.TateGlobal.ideleNorm_pos (F := L) (uτ K L D τ x)
  have h2 := NumberField.TateGlobal.ideleNorm_pos (F := L) x
  nlinarith [h, h1, h2, sq_nonneg (NumberField.TateGlobal.ideleNorm L (uτ K L D τ x) - NumberField.TateGlobal.ideleNorm L x),
    sq_nonneg (NumberField.TateGlobal.ideleNorm L (uτ K L D τ x) + NumberField.TateGlobal.ideleNorm L x)]

theorem ideleNorm_cN (w : II L) :
    NumberField.TateGlobal.ideleNorm L (cN K L σ D w) = NumberField.TateGlobal.ideleNorm L w ^ orderOf σ := by
  rw [← normHom_apply, cN_apply, map_prod]
  have : ∀ k ∈ Finset.range (orderOf σ), normHom L (D.unitsAct (σ ^ k) w) = normHom L w := fun k _ =>
    ideleNorm_uτ K L D (σ ^ k) w
  rw [Finset.prod_congr rfl this, Finset.prod_const, Finset.card_range, normHom_apply]

theorem orderOf_pos_aut : 0 < orderOf σ := by
  let f : (L ≃ₐ[K] L) → (L ≃ₐ[ℚ] L) := fun τ => AlgEquiv.ofRingEquiv (f := (τ : L ≃+* L)) (fun q => by simp)
  have hf : Function.Injective f := by
    intro a b h
    ext x
    exact congrArg (fun e : L ≃ₐ[ℚ] L => e x) h
  haveI : Finite (L ≃ₐ[K] L) := Finite.of_injective f hf
  exact orderOf_pos σ

theorem uτ_ι (τ : L ≃ₐ[K] L) (η : Lˣ) : uτ K L D τ (ι L η) = ι L (Units.map (τ : L →* L) η) :=
  Units.ext (D.compat τ (η : L))

def cNL : Lˣ →* Lˣ := ∏ k ∈ Finset.range (orderOf σ), Units.map ((σ ^ k : L ≃ₐ[K] L) : L →* L)

theorem cN_ι (η : Lˣ) : cN K L σ D (ι L η) = ι L (cNL K L σ η) := by
  unfold cN cNL
  rw [MonoidHom.finsetProd_apply, MonoidHom.finsetProd_apply, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  exact uτ_ι K L D (σ ^ k) η

theorem exists_isCompact_forall_exists_ideleNorm_eq (a b : ℝ) (ha : 0 < a) :
    ∃ R : Set (II L), IsCompact R ∧ ∀ t ∈ Set.Icc a b, ∃ r ∈ R, NumberField.TateGlobal.ideleNorm L r = t := by
  obtain ⟨s, hs, hsn, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq L

  have hpos : ∀ t : Set.Icc a b, (0 : ℝ) < t := fun t => lt_of_lt_of_le ha t.2.1
  let ψ : Set.Icc a b → ℝ≥0ˣ := fun t =>
    ⟨⟨(t : ℝ), (hpos t).le⟩, ⟨(t : ℝ)⁻¹, inv_nonneg.mpr (hpos t).le⟩,
      NNReal.eq (mul_inv_cancel₀ (hpos t).ne'), NNReal.eq (inv_mul_cancel₀ (hpos t).ne')⟩
  have hψval : ∀ t : Set.Icc a b, ((ψ t : ℝ≥0ˣ) : ℝ≥0) = ⟨(t : ℝ), (hpos t).le⟩ := fun t => rfl
  have hψinv : ∀ t : Set.Icc a b, (((ψ t)⁻¹ : ℝ≥0ˣ) : ℝ≥0) = ⟨(t : ℝ)⁻¹, inv_nonneg.mpr (hpos t).le⟩ :=
    fun t => rfl
  have hψc : Continuous ψ := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · have : (Units.val ∘ ψ) = fun t : Set.Icc a b => (⟨(t : ℝ), (hpos t).le⟩ : ℝ≥0) := by
        funext t; exact hψval t
      rw [this]
      exact continuous_subtype_val.subtype_mk _
    · have : (fun t : Set.Icc a b => (((ψ t)⁻¹ : ℝ≥0ˣ) : ℝ≥0)) =
          fun t : Set.Icc a b => (⟨(t : ℝ)⁻¹, inv_nonneg.mpr (hpos t).le⟩ : ℝ≥0) := by
        funext t; exact hψinv t
      rw [this]
      exact (continuous_subtype_val.inv₀ fun t => (hpos t).ne').subtype_mk _
  refine ⟨Set.range (fun t : Set.Icc a b => s (ψ t)), isCompact_range (hs.comp hψc), ?_⟩
  intro t ht
  refine ⟨s (ψ ⟨t, ht⟩), ⟨⟨t, ht⟩, rfl⟩, ?_⟩
  rw [hsn, hψval]
  rfl

theorem finite_setOf_ι_mem {C : Set (II L)} (hC : IsCompact C) : {ν : Lˣ | ι L ν ∈ C}.Finite := by
  have hC' : IsCompact ((Units.val : II L → AdeleRing (𝓞 L) L) '' C) := hC.image Units.continuous_val
  have hfin := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L hC'
  have hfin' : ((Units.val : Lˣ → L) ⁻¹' {ξ : L | algebraMap L (AdeleRing (𝓞 L) L) ξ ∈
      (Units.val : II L → AdeleRing (𝓞 L) L) '' C}).Finite :=
    hfin.preimage Units.val_injective.injOn
  refine hfin'.subset ?_
  intro ν hν
  exact ⟨ι L ν, hν, rfl⟩

theorem exists_isCompact_inter_subset_image {C : Set (II L)} (hC : IsCompact C) :
    ∃ W : Set (II L), IsCompact W ∧ Set.range (cN K L σ D) ∩ C ⊆ cN K L σ D '' W := by
  classical
  by_cases hCne : C.Nonempty
  swap
  · refine ⟨∅, isCompact_empty, ?_⟩
    rw [Set.not_nonempty_iff_eq_empty.mp hCne, Set.inter_empty]
    exact Set.empty_subset _
  have hn : 0 < orderOf σ := orderOf_pos_aut K L σ

  have hNC : IsCompact (NumberField.TateGlobal.ideleNorm L '' C) :=
    hC.image (NumberField.TateGlobal.continuous_ideleNorm L)
  obtain ⟨m, ⟨y₀, hy₀, rfl⟩, hm⟩ := hNC.exists_isLeast (hCne.image _)
  obtain ⟨M, -, hM⟩ := hNC.exists_isGreatest (hCne.image _)
  set a : ℝ := min 1 (NumberField.TateGlobal.ideleNorm L y₀) with ha
  set b : ℝ := max 1 M with hb
  have ha0 : 0 < a := lt_min one_pos (NumberField.TateGlobal.ideleNorm_pos y₀)

  obtain ⟨R, hRc, hR⟩ := exists_isCompact_forall_exists_ideleNorm_eq L a b ha0
  obtain ⟨K₁, hK₁c, -, hK₁⟩ :=
    NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul L
  have hRK : IsCompact (R * K₁) := hRc.mul hK₁c
  have hK' : IsCompact ((cN K L σ D '' (R * K₁))⁻¹ * C) := ((hRK.image (continuous_cN K L σ D)).inv).mul hC

  have hfin := finite_setOf_ι_mem L hK'
  set good : Set Lˣ := {ν : Lˣ | ι L ν ∈ (cN K L σ D '' (R * K₁))⁻¹ * C ∧ ∃ η : Lˣ, cNL K L σ η = ν} with hgood
  have hgoodfin : good.Finite := hfin.subset fun ν hν => hν.1

  let g : Lˣ → Lˣ := fun ν => Classical.epsilon fun η : Lˣ => cNL K L σ η = ν
  have hg : ∀ ν ∈ good, cNL K L σ (g ν) = ν := fun ν hν => Classical.epsilon_spec hν.2
  set E : Set (II L) := (fun ν => ι L (g ν)) '' good with hE
  have hEc : IsCompact E := (hgoodfin.image _).isCompact
  refine ⟨R * K₁ * E, hRK.mul hEc, ?_⟩

  rintro x ⟨⟨w, rfl⟩, hxC⟩

  set t : ℝ := NumberField.TateGlobal.ideleNorm L w with ht
  have htpos : 0 < t := NumberField.TateGlobal.ideleNorm_pos w
  have htn : t ^ orderOf σ ∈ Set.Icc (NumberField.TateGlobal.ideleNorm L y₀) M := by
    rw [ht, ← ideleNorm_cN]
    exact ⟨hm ⟨_, hxC, rfl⟩, hM ⟨_, hxC, rfl⟩⟩
  have htab : t ∈ Set.Icc a b := by
    constructor
    · rcases le_or_gt a t with hle | hlt
      · exact hle
      · exfalso
        have ht1 : t ≤ 1 := (le_of_lt hlt).trans (min_le_left _ _)
        have h1 : t ^ orderOf σ ≤ t := pow_le_of_le_one htpos.le ht1 hn.ne'
        have h2 : t ^ orderOf σ < NumberField.TateGlobal.ideleNorm L y₀ :=
          lt_of_le_of_lt h1 (lt_of_lt_of_le hlt (min_le_right _ _))
        exact absurd htn.1 (not_le.mpr h2)
    · rcases le_or_gt t b with hle | hlt
      · exact hle
      · exfalso
        have ht1 : 1 ≤ t := (le_max_left _ _).trans (le_of_lt hlt)
        have h1 : t ≤ t ^ orderOf σ := le_self_pow₀ ht1 hn.ne'
        have h2 : M < t ^ orderOf σ := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hlt) h1
        exact absurd htn.2 (not_le.mpr h2)
  obtain ⟨r, hrR, hrt⟩ := hR t htab

  have hwr : w * r⁻¹ ∈ NumberField.TateGlobal.normOneIdeles L := by
    rw [NumberField.TateGlobal.mem_normOneIdeles_iff, ← normHom_apply, map_mul, map_inv, normHom_apply,
      normHom_apply, hrt, ← ht, mul_inv_cancel₀ htpos.ne']
  obtain ⟨η, κ, hκ, hwr'⟩ := hK₁ _ hwr
  have hw : w = r * κ * ι L η := by
    have : w = (w * r⁻¹) * r := by rw [inv_mul_cancel_right]
    rw [this, hwr']
    show (ι L η) * κ * r = r * κ * ι L η
    rw [mul_comm (ι L η) κ, mul_comm _ r, ← mul_assoc]

  set ν : Lˣ := cNL K L σ η with hν
  have hνmem : ι L ν ∈ (cN K L σ D '' (R * K₁))⁻¹ * C := by
    refine Set.mem_mul.mpr ⟨(cN K L σ D (r * κ))⁻¹, ?_, cN K L σ D w, hxC, ?_⟩
    · exact Set.inv_mem_inv.mpr ⟨r * κ, Set.mul_mem_mul hrR hκ, rfl⟩
    · rw [hw, map_mul (cN K L σ D) (r * κ) (ι L η), cN_ι, ← hν, inv_mul_cancel_left]
  have hνgood : ν ∈ good := ⟨hνmem, η, rfl⟩

  refine ⟨r * κ * ι L (g ν), Set.mul_mem_mul (Set.mul_mem_mul hrR hκ) ⟨ν, hνgood, rfl⟩, ?_⟩
  show cN K L σ D (r * κ * ι L (g ν)) = cN K L σ D w
  rw [map_mul (cN K L σ D) (r * κ) (ι L (g ν)), cN_ι, hg ν hνgood, hw,
    map_mul (cN K L σ D) (r * κ) (ι L η), cN_ι, ← hν]

theorem locallyCompactSpace_II : LocallyCompactSpace (II L) :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem main :
    IsClosed (Set.range fun w : (AdeleRing (𝓞 L) L)ˣ =>
      ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) w) := by
  haveI := locallyCompactSpace_II L
  rw [← range_cN_eq]
  refine isClosed_of_closure_subset ?_
  intro x hx
  obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds x
  obtain ⟨W, hWc, hW⟩ := exists_isCompact_inter_subset_image K L σ D hCc
  have h1 : x ∈ closure (Set.range (cN K L σ D) ∩ C) := by
    rw [mem_closure_iff_nhds] at hx ⊢
    intro t ht
    obtain ⟨y, hyt, hyS⟩ := hx (t ∩ C) (inter_mem ht hCn)
    exact ⟨y, hyt.1, hyS, hyt.2⟩
  have h2 : closure (Set.range (cN K L σ D) ∩ C) ⊆ cN K L σ D '' W :=
    closure_minimal hW ((hWc.image (continuous_cN K L σ D)).isClosed)
  obtain ⟨w, -, hw⟩ := h2 h1
  exact ⟨w, hw⟩

end Main

end R4NC

end

open NumberField in
theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) :
    IsClosed (Set.range fun w : (AdeleRing (𝓞 L) L)ˣ =>
      ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) w) :=
  R4NC.main K L σ D

end S_M4aHerbrand_IdeleGaloisDescent_isClosed_range_prod_unitsAct_pow
end P2MW
export P2MW.S_M4aHerbrand_IdeleGaloisDescent_isClosed_range_prod_unitsAct_pow (solution)
