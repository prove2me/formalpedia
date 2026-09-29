-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6ca1c3f4-c169-52a0-a0e9-7f39512c5128

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm

section Fold_LocalHaarModulus

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set

open scoped NNReal ENNReal Pointwise

namespace M4aLocalCFT

namespace LocalHaarModulus

noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem card_residueField_eq_absNorm :
    Nat.card (ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField F v).toEquiv.symm

section CosetStep

variable {F v}

private theorem exists_out_add_mul {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (Y : v.adicCompletionIntegers F) :
    ∃ z : v.adicCompletionIntegers F,
      Y = Quotient.out (residue (v.adicCompletionIntegers F) Y) + ϖ * z := by
  have hout : residue (v.adicCompletionIntegers F)
      (Quotient.out (residue (v.adicCompletionIntegers F) Y))
      = residue (v.adicCompletionIntegers F) Y := Quotient.out_eq _
  have hzero : residue (v.adicCompletionIntegers F)
      (Y - Quotient.out (residue (v.adicCompletionIntegers F) Y)) = 0 := by
    rw [map_sub, hout, sub_self]
  set w : v.adicCompletionIntegers F
      := Y - Quotient.out (residue (v.adicCompletionIntegers F) Y) with hw
  have hmem : w ∈ maximalIdeal (v.adicCompletionIntegers F) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, ?_⟩
  have hsub : Y - Quotient.out (residue (v.adicCompletionIntegers F) Y) = ϖ * z := by
    rw [← hw]; exact hz
  exact sub_eq_iff_eq_add'.mp hsub

private theorem residue_out_add_mul {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (k : ResidueField (v.adicCompletionIntegers F)) (z : v.adicCompletionIntegers F) :
    residue (v.adicCompletionIntegers F) (Quotient.out k + ϖ * z) = k := by
  have hϖ0 : residue (v.adicCompletionIntegers F) ϖ = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [hϖ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self ϖ
  have hout : residue (v.adicCompletionIntegers F) (Quotient.out k) = k := Quotient.out_eq _
  rw [map_add, map_mul, hϖ0, zero_mul, add_zero, hout]

private abbrev cosetMap (ϖ : v.adicCompletionIntegers F)
    (k : ResidueField (v.adicCompletionIntegers F)) (y : v.adicCompletion F) :
    v.adicCompletion F :=
  ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F)
    + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * y

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in
private theorem integers_eq_iUnion_image {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = ⋃ k : ResidueField (v.adicCompletionIntegers F),
          cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := exists_out_add_mul hϖ (⟨y, hy⟩ : v.adicCompletionIntegers F)
    refine mem_iUnion.mpr ⟨residue (v.adicCompletionIntegers F) ⟨y, hy⟩, ?_⟩
    refine ⟨(z : v.adicCompletion F), z.2, ?_⟩
    have hco := congrArg
      (fun w : v.adicCompletionIntegers F => (w : v.adicCompletion F)) hz
    push_cast at hco
    exact hco.symm
  · intro hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    obtain ⟨z, hz, hzy⟩ := hk
    obtain ⟨X, hXy⟩ : ∃ X : v.adicCompletionIntegers F, (X : v.adicCompletion F) = y :=
      ⟨Quotient.out k + ϖ * ⟨z, hz⟩, by push_cast; exact hzy⟩
    rw [← hXy]
    exact X.2

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in
private theorem pairwise_disjoint_image {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Pairwise (Function.onFun Disjoint fun k : ResidueField (v.adicCompletionIntegers F) =>
      cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  intro k k' hkk'
  refine Set.disjoint_left.mpr fun y hy hy' => hkk' ?_
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨z', hz', hzy'⟩ := hy'
  have hKeq : ((Quotient.out k + ϖ * ⟨z, hz⟩ : v.adicCompletionIntegers F) :
      v.adicCompletion F)
      = ((Quotient.out k' + ϖ * ⟨z', hz'⟩ : v.adicCompletionIntegers F) :
          v.adicCompletion F) := by
    push_cast
    rw [show ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F)
          + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * z = y from hzy,
        show ((Quotient.out k' : v.adicCompletionIntegers F) : v.adicCompletion F)
          + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * z' = y from hzy']
  have hAeq : (Quotient.out k + ϖ * ⟨z, hz⟩ : v.adicCompletionIntegers F)
      = (Quotient.out k' + ϖ * ⟨z', hz'⟩ : v.adicCompletionIntegers F) :=
    Subtype.coe_injective hKeq
  have := congrArg (residue (v.adicCompletionIntegers F)) hAeq
  rwa [residue_out_add_mul hϖ, residue_out_add_mul hϖ] at this

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in
private theorem cosetMap_image_eq {ϖ : v.adicCompletionIntegers F}
    (k : ResidueField (v.adicCompletionIntegers F)) :
    cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
          (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  rw [← Set.image_vadd, ← Set.image_smul, ← Set.image_comp]
  rfl

end CosetStep

section Measure

variable {F v}

set_option maxHeartbeats 6400000 in
set_option maxSynthPendingDepth 3 in
private theorem measure_integers_eq_card_mul [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F))
    [μ.IsAddHaarMeasure] {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞)
        * μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  have hϖ0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    simpa using (Subtype.coe_injective.ne_iff.mpr hϖ.ne_zero)
  have hTopen : IsOpen (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    (NumberField.isOpenAdicCompletionIntegers F v).smul₀ hϖ0
  have hTmeas := hTopen.measurableSet
  have hbridge : ∀ k : ResidueField (v.adicCompletionIntegers F),
      cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
        = ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
            (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
              (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun k => cosetMap_image_eq k
  calc μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = μ (⋃ k : ResidueField (v.adicCompletionIntegers F),
          cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        rw [← integers_eq_iUnion_image hϖ]
    _ = ∑' k : ResidueField (v.adicCompletionIntegers F),
          μ (cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        refine measure_iUnion ?_ fun k => ?_
        · intro k k' hkk'
          exact pairwise_disjoint_image hϖ hkk'
        · rw [hbridge k]
          exact hTmeas.const_vadd _
    _ = ∑' k : ResidueField (v.adicCompletionIntegers F),
          μ (((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
            (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
              (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) := by
        exact tsum_congr fun k => by rw [hbridge k]
    _ = ∑' _ : ResidueField (v.adicCompletionIntegers F),
          μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        refine tsum_congr fun k => ?_
        exact measure_vadd _ _ _
    _ = (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞)
        * μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        haveI : Fintype (ResidueField (v.adicCompletionIntegers F)) := Fintype.ofFinite _
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Nat.card_eq_fintype_card]

end Measure

section MainTheorem

variable {F v}

private theorem distribHaarChar_eq_one_of_mem_range (x : (v.adicCompletion F)ˣ)
    (hx : x ∈ (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)).range) :
    distribHaarChar (v.adicCompletion F) x = 1 := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  haveI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  obtain ⟨u, rfl⟩ := hx
  set S := (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hS
  have hK : IsCompact S := NumberField.isCompactAdicCompletionIntegers F v
  have hO : IsOpen S := NumberField.isOpenAdicCompletionIntegers F v
  obtain ⟨μ⟩ : Nonempty {μ : Measure (v.adicCompletion F) // μ.IsAddHaarMeasure ∧ μ.Regular} :=
    ⟨⟨(MeasureTheory.Measure.addHaarMeasure
        ⟨⟨S, hK⟩, by
          rw [interior_eq_iff_isOpen.mpr hO]
          exact ⟨0, Subring.zero_mem _⟩⟩),
      inferInstance, inferInstance⟩⟩
  obtain ⟨μ, hHaar, hReg⟩ := μ
  haveI := hHaar; haveI := hReg
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := S)
    (hO.measure_ne_zero μ ⟨0, Subring.zero_mem _⟩) (hK.measure_lt_top.ne) ?_
  have hset : ((Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)) u : _) • S = S := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mul_mem ((u : v.adicCompletionIntegers F).2) hz
    · intro hy
      set w : v.adicCompletionIntegers F := ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) :
        v.adicCompletionIntegers F) with hw
      refine ⟨(w : v.adicCompletion F) * y, mul_mem w.2 hy, ?_⟩
      have hcancel : ((u : v.adicCompletionIntegers F) : v.adicCompletion F)
          * (w : v.adicCompletion F) = 1 := by
        have : ((u : v.adicCompletionIntegers F) * w : v.adicCompletionIntegers F)
            = (1 : v.adicCompletionIntegers F) := by
          rw [hw]
          exact_mod_cast u.mul_inv
        calc ((u : v.adicCompletionIntegers F) : v.adicCompletion F) * (w : v.adicCompletion F)
            = (((u : v.adicCompletionIntegers F) * w : v.adicCompletionIntegers F) :
                v.adicCompletion F) := by rw [Subring.coe_mul]
          _ = 1 := by rw [this]; rfl
      show ((u : v.adicCompletionIntegers F) : v.adicCompletion F)
          * ((w : v.adicCompletion F) * y) = y
      rw [← mul_assoc, hcancel, one_mul]
  rw [hset, ENNReal.coe_one, one_mul]

private theorem distribHaarChar_mk0_irreducible {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (h0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0) :
    distribHaarChar (v.adicCompletion F) (Units.mk0 _ h0)
      = ((Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0))⁻¹ := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  haveI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  set S := (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hS
  have hK : IsCompact S := NumberField.isCompactAdicCompletionIntegers F v
  have hO : IsOpen S := NumberField.isOpenAdicCompletionIntegers F v
  set μ : Measure (v.adicCompletion F) := MeasureTheory.Measure.addHaarMeasure
    ⟨⟨S, hK⟩, by
      rw [interior_eq_iff_isOpen.mpr hO]
      exact ⟨0, Subring.zero_mem _⟩⟩ with hμ
  have hq0 : (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp Nat.card_pos
  have hS0 : μ S ≠ 0 := hO.measure_ne_zero μ ⟨0, Subring.zero_mem _⟩
  have hSfin : μ S ≠ ⊤ := hK.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := S) hS0 hSfin ?_
  have hcount := measure_integers_eq_card_mul μ hϖ
  show μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) • S)
      = ((Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0))⁻¹ * μ S
  rw [ENNReal.coe_inv (by exact_mod_cast Nat.pos_iff_ne_zero.mp Nat.card_pos), ENNReal.coe_natCast]
  rw [hcount]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 (ENNReal.natCast_ne_top _), one_mul]

end MainTheorem

end

end LocalHaarModulus

end M4aLocalCFT

end Fold_LocalHaarModulus

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.modulus"
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "modulus modulus_zero modulus_coe_units localBorel borelSpace_localBorel integersPositiveCompacts coe_integersPositiveCompacts"
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped NNReal ENNReal Pointwise WithZero

section PortModulus

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

attribute [local instance] localBorel borelSpace_localBorel

private theorem smul_coe_adicCompletionIntegers_eq (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) :
    u • (v.adicCompletionIntegers K : Set (v.adicCompletion K))
      = (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, SetLike.mem_coe,
    mem_adicCompletionIntegers, mem_adicCompletionIntegers, Units.smul_def, smul_eq_mul, map_mul,
    Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one, one_mul]

private theorem modulus_eq_one_of_valued_eq_one (u : (v.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.adicCompletion K) = 1) : modulus (u : v.adicCompletion K) = 1 := by
  rw [modulus_coe_units]
  have hself : Measure.addHaarMeasure (integersPositiveCompacts K v)
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1 := by
    rw [← coe_integersPositiveCompacts K v]
    exact Measure.addHaarMeasure_self
  refine distribHaarChar_eq_of_measure_smul_eq_mul
    (μ := Measure.addHaarMeasure (integersPositiveCompacts K v))
    (s := (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ?_ ?_ ?_
  · rw [hself]; exact one_ne_zero
  · rw [hself]; exact ENNReal.one_ne_top
  · rw [smul_coe_adicCompletionIntegers_eq K v u hu, hself, ENNReal.coe_one, one_mul]

private theorem withZero_lt_one_iff_le_exp_neg_one (x : ℤᵐ⁰) : x < 1 ↔ x ≤ WithZero.exp (-1 : ℤ) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add]
  norm_num

private theorem isUnit_adicCompletionIntegers_iff (a : v.adicCompletionIntegers K) :
    IsUnit a ↔ Valued.v (a : v.adicCompletion K) = 1 := by
  rw [ValuationSubring.valuation_eq_one_iff]
  exact ((Valuation.isEquiv_valuation_valuationSubring Valued.v).eq_one_iff_eq_one).symm

private theorem uniformizerUnit_mem :
    (uniformizerUnit K v : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
  rw [mem_adicCompletionIntegers, valued_uniformizerUnit, ← WithZero.exp_zero]
  exact WithZero.exp_le_exp.mpr (by norm_num)

private def uniformizerInt : v.adicCompletionIntegers K := ⟨_, uniformizerUnit_mem K v⟩

@[scoped simp] private theorem coe_uniformizerInt :
    (uniformizerInt K v : v.adicCompletion K) = uniformizerUnit K v := rfl

private theorem irreducible_uniformizerInt : Irreducible (uniformizerInt K v) := by
  have hϖ : Valued.v ((uniformizerInt K v : v.adicCompletionIntegers K) : v.adicCompletion K)
      = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit K v
  refine irreducible_iff.mpr ⟨?_, ?_⟩
  · rw [isUnit_adicCompletionIntegers_iff, hϖ, ← WithZero.exp_zero]
    exact fun h => by norm_num [WithZero.exp_inj] at h
  · intro a b hab
    have ha : Valued.v (a : v.adicCompletion K) ≤ 1 := (mem_adicCompletionIntegers (𝓞 K) K v).mp a.2
    have hb : Valued.v (b : v.adicCompletion K) ≤ 1 := (mem_adicCompletionIntegers (𝓞 K) K v).mp b.2
    have hprod : Valued.v (a : v.adicCompletion K) * Valued.v (b : v.adicCompletion K)
        = WithZero.exp (-1 : ℤ) := by
      rw [← map_mul, ← MulMemClass.coe_mul, ← hab, hϖ]
    rw [isUnit_adicCompletionIntegers_iff, isUnit_adicCompletionIntegers_iff]
    by_contra h
    push Not at h
    have ha' : Valued.v (a : v.adicCompletion K) ≤ WithZero.exp (-1 : ℤ) :=
      (withZero_lt_one_iff_le_exp_neg_one _).mp (lt_of_le_of_ne ha h.1)
    have hb' : Valued.v (b : v.adicCompletion K) ≤ WithZero.exp (-1 : ℤ) :=
      (withZero_lt_one_iff_le_exp_neg_one _).mp (lt_of_le_of_ne hb h.2)
    have hle := mul_le_mul' ha' hb'
    rw [hprod, ← WithZero.exp_add, WithZero.exp_le_exp] at hle
    norm_num at hle

private theorem modulus_uniformizerUnit :
    modulus (uniformizerUnit K v : v.adicCompletion K) = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
  have h0 : ((uniformizerInt K v : v.adicCompletionIntegers K) : v.adicCompletion K) ≠ 0 :=
    (uniformizerUnit K v).ne_zero
  have hmk : Units.mk0 _ h0 = uniformizerUnit K v := Units.ext rfl
  have h := M4aLocalCFT.LocalHaarModulus.distribHaarChar_mk0_irreducible
    (irreducible_uniformizerInt K v) h0
  rw [hmk, M4aLocalCFT.LocalHaarModulus.card_residueField_eq_absNorm K v] at h
  rw [modulus_coe_units, h]

private theorem toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by
  have h : WithZero.unzero (WithZero.exp_ne_zero : WithZero.exp n ≠ 0) = Multiplicative.ofAdd n :=
    WithZero.unzero_coe _
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero, h, toAdd_ofAdd]

private theorem modulus_eq_toNNReal_valued (x : v.adicCompletion K) :
    modulus x = WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
      (Valued.v x) := by
  by_cases hx : x = 0
  · subst hx
    rw [modulus_zero, map_zero, map_zero]
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v x = WithZero.exp n :=
    ⟨WithZero.log (Valued.v x), (WithZero.exp_log hvx).symm⟩
  set ϖ : (v.adicCompletion K)ˣ := uniformizerUnit K v with hϖ_def
  set u : (v.adicCompletion K)ˣ := Units.mk0 x hx * ϖ ^ n with hu_def
  have hu : Valued.v (u : v.adicCompletion K) = 1 := by
    rw [hu_def, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0, hn,
      hϖ_def, valued_uniformizerUnit, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one,
      ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  have hx_eq : Units.mk0 x hx = u * ϖ ^ (-n) := by
    rw [hu_def, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  have hmod : modulus x = distribHaarChar (v.adicCompletion K) (Units.mk0 x hx) := by
    rw [← modulus_coe_units, Units.val_mk0]
  have hϖmod : distribHaarChar (v.adicCompletion K) ϖ = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
    rw [← modulus_coe_units, hϖ_def, modulus_uniformizerUnit]
  have humod : distribHaarChar (v.adicCompletion K) u = 1 := by
    rw [← modulus_coe_units]
    exact modulus_eq_one_of_valued_eq_one K v u hu
  rw [hmod, hx_eq, map_mul, map_zpow, humod, hϖmod, one_mul, inv_zpow', neg_neg, hn,
    toNNReal_exp]

private theorem coe_modulus_eq_norm (x : v.adicCompletion K) : (modulus x : ℝ) = ‖x‖ := by
  rw [modulus_eq_toNNReal_valued, NumberField.FinitePlace.norm_def]

end PortModulus

end LanglandsTunnell.TateLocal
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm.LanglandsTunnell.TateLocal"
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm.LanglandsTunnell"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm.LanglandsTunnell P2MW.S_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm.LanglandsTunnell.TateLocal"

p2m_open "LanglandsTunnell.TateLocal P2MW.S_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm.LanglandsTunnell.TateLocal"

theorem solution (K : Type) [Field K]
    [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion K v) :
    modulus x = ‖x‖₊ :=
  NNReal.coe_injective
    ((LanglandsTunnell.TateLocal.coe_modulus_eq_norm K v x).trans (coe_nnnorm x).symm)

end S_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm (solution)
