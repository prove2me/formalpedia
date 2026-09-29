-- Prove2me | solution 1 for LanglandsTunnell.Converse.exists_isJLNice_of_forall_isNicePinned
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8141a8c9-9947-5fe2-a223-077c3cbf0b43

import Definitions.Def_LanglandsTunnell_JLData
import Theorems.Thm_LanglandsTunnell_TateLocal_exists_hasConductorExponentAt_of_continuous
import Theorems.Thm_LanglandsTunnell_Converse_exists_ne_zero_valuation_eq_exp_neg
import Theorems.Thm_NumberField_TateGlobal_continuous_localChar
import Theorems.Thm_LanglandsTunnell_Converse_sPart_shift
import Theorems.Thm_LanglandsTunnell_Converse_sPartDual_eq_sPart_inv
import Theorems.Thm_LanglandsTunnell_Converse_nonempty_sOrderReps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_exists_isJLNice_of_forall_isNicePinned

set_option autoImplicit false

noncomputable section

open scoped WithZero
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.TateGlobal NumberField.StandardAddChar
open AutomorphicForm
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_Converse_exists_isJLNice_of_forall_isNicePinned.LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.Converse P2MW.S_LanglandsTunnell_Converse_exists_isJLNice_of_forall_isNicePinned.LanglandsTunnell.Converse"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "RealArchParam ComplexArchParam"
namespace Converse
p2m_export "LanglandsTunnell.Converse" "localOf IsOneMod IsSUnit sWeight JLData SOrderReps JLData.sSum JLData.sSumDual JLData.sFactor IsJLNice finiteConductor pinnedRootNumber IsAdmissibleTwist IsArchCompAt twistedDatum IsNicePinned sPart sPartDual exists_ne_zero_valuation_eq_exp_neg sPart_shift sPartDual_eq_sPart_inv nonempty_sOrderReps"
namespace ShiftedFamily
p2m_open "LanglandsTunnell.Converse LanglandsTunnell"

section Generic

variable {F : Type*} [Field F] [Valued F ℤᵐ⁰]

private def valOrd (x : Fˣ) : ℤ := -WithZero.log (Valued.v (x : F))

private theorem v_ne_zero (x : Fˣ) : Valued.v (x : F) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr x.ne_zero

private theorem v_eq_exp_neg_valOrd (x : Fˣ) : Valued.v (x : F) = WithZero.exp (-valOrd x) := by
  rw [valOrd, neg_neg, WithZero.exp_log (v_ne_zero x)]

private theorem valOrd_eq_iff (x : Fˣ) (n : ℤ) :
    valOrd x = n ↔ Valued.v (x : F) = WithZero.exp (-n) := by
  rw [v_eq_exp_neg_valOrd, WithZero.exp_inj, neg_inj]

private theorem valOrd_mul (x y : Fˣ) : valOrd (x * y) = valOrd x + valOrd y := by
  simp only [valOrd, Units.val_mul, map_mul, WithZero.log_mul (v_ne_zero x) (v_ne_zero y), neg_add]

private theorem valOrd_eq_zero_of_v_eq_one {y : Fˣ} (hy : Valued.v (y : F) = 1) : valOrd y = 0 := by
  simp [valOrd, hy]

private theorem valOrd_mul_of_v_eq_one (x : Fˣ) {y : Fˣ} (hy : Valued.v (y : F) = 1) :
    valOrd (x * y) = valOrd x := by
  rw [valOrd_mul, valOrd_eq_zero_of_v_eq_one hy, add_zero]

private theorem valOrd_zpow (π : Fˣ) (hπ : Valued.v (π : F) = WithZero.exp (-1)) (n : ℤ) :
    valOrd (π ^ n) = n := by
  rw [valOrd_eq_iff, Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_neg, zsmul_one,
    Int.cast_id]

private def valUnitPart (π : Fˣ) (x : Fˣ) : Fˣ := x * π ^ (-valOrd x)

private theorem eq_valUnitPart_mul_zpow (π x : Fˣ) : x = valUnitPart π x * π ^ valOrd x := by
  rw [valUnitPart, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]

private theorem v_valUnitPart {π : Fˣ} (hπ : Valued.v (π : F) = WithZero.exp (-1)) (x : Fˣ) :
    Valued.v (valUnitPart π x : F) = 1 := by
  have h := v_eq_exp_neg_valOrd (valUnitPart π x)
  rw [h, WithZero.exp_eq_one, neg_eq_zero, valUnitPart, valOrd_mul, valOrd_zpow π hπ, add_neg_cancel]

private theorem valUnitPart_mul_of_v_eq_one (π x : Fˣ) {y : Fˣ} (hy : Valued.v (y : F) = 1) :
    valUnitPart π (x * y) = valUnitPart π x * y := by
  rw [valUnitPart, valUnitPart, valOrd_mul_of_v_eq_one x hy, mul_right_comm]

private theorem norm_apply_eq_one_of_continuous (hc : IsCompact {x : F | Valued.v x = 1}) (χ : Fˣ →* ℂˣ)
    (hχ : Continuous χ) (u : Fˣ) (hu : Valued.v (u : F) = 1) : ‖((χ u : ℂˣ) : ℂ)‖ = 1 := by
  set U : Set Fˣ := {x | Valued.v (x : F) = 1} with hU
  have himg : (Units.val : Fˣ → F) '' U = {x : F | Valued.v x = 1} := by
    ext x
    refine ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ?_⟩
    have hx0 : x ≠ 0 := fun h => by simp [h] at hx
    exact ⟨Units.mk0 x hx0, hx, rfl⟩
  have hUc : IsCompact U := by
    rw [Units.isEmbedding_val₀.isCompact_iff, himg]
    exact hc
  set f : Fˣ → ℝ := fun x => ‖((χ x : ℂˣ) : ℂ)‖ with hf
  have hfc : Continuous f := continuous_norm.comp (Units.continuous_val.comp hχ)
  obtain ⟨M, hM⟩ := (hUc.image hfc).bddAbove
  have hle : ∀ w : Fˣ, Valued.v (w : F) = 1 → f w ≤ 1 := by
    intro w hw
    by_contra h
    rw [not_le] at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h
    have hmem : f (w ^ n) ∈ f '' U := ⟨w ^ n, by simp [hU, hw], rfl⟩
    have h1 : f (w ^ n) = f w ^ n := by simp [hf]
    exact (lt_irrefl M) (hn.trans_le (h1 ▸ hM hmem))
  have h1 := hle u hu
  have h2 := hle u⁻¹ (by simp [hu])
  have hfinv : f u⁻¹ = (f u)⁻¹ := by simp [hf]
  have hpos : 0 < f u := by simp [hf]
  rw [hfinv, inv_le_one₀ hpos] at h2
  exact le_antisymm h1 h2

end Generic

variable {K : Type} [Field K] [NumberField K] {S : Finset (HeightOneSpectrum (𝓞 K))}

private def ordVecS (α : Kˣ) : ↥S → ℤ := fun v => valOrd (localOf K v.1 α)

private def unitPartS (v : ↥S) (α : Kˣ) : (v.1.adicCompletion K)ˣ :=
  valUnitPart (uniformizerUnit K v.1) (localOf K v.1 α)

private theorem v_uniformizerUnit (v : ↥S) :
    Valued.v ((uniformizerUnit K v.1 : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) = WithZero.exp (-1) :=
  valued_uniformizerUnit K v.1

private theorem v_unitPartS (v : ↥S) (α : Kˣ) :
    Valued.v ((unitPartS v α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) = 1 :=
  v_valUnitPart (v_uniformizerUnit v) _

private theorem localOf_eq_unitPartS_mul (v : ↥S) (α : Kˣ) :
    localOf K v.1 α = unitPartS v α * uniformizerUnit K v.1 ^ ordVecS α v :=
  eq_valUnitPart_mul_zpow _ _

private theorem ordVecS_eq_iff (α : Kˣ) (n : ↥S → ℤ) :
    ordVecS α = n ↔ ∀ v : ↥S, Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K)
      = WithZero.exp (-(n v)) := by
  simp only [funext_iff, ordVecS, valOrd_eq_iff]

private theorem ordVecS_rep (R : SOrderReps K S) (n : ↥S → ℤ) : ordVecS (R.rep n) = n :=
  (ordVecS_eq_iff _ _).mpr (R.rep_ord n)

private theorem localOf_mul (v : ↥S) (α β : Kˣ) :
    localOf K v.1 (α * β) = localOf K v.1 α * localOf K v.1 β :=
  map_mul _ _ _

private theorem ordVecS_mul_of_isSUnit (α β : Kˣ) (hβ : IsSUnit K S β) :
    ordVecS (S := S) (α * β) = ordVecS α := by
  funext v
  simp only [ordVecS, localOf_mul]
  exact valOrd_mul_of_v_eq_one _ (hβ v)

private theorem unitPartS_mul_of_isSUnit (v : ↥S) (α β : Kˣ) (hβ : IsSUnit K S β) :
    unitPartS v (α * β) = unitPartS v α * localOf K v.1 β := by
  simp only [unitPartS, localOf_mul]
  exact valUnitPart_mul_of_v_eq_one _ _ (hβ v)

section Families

variable (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
  (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)

private def coeffA (A : (↥S → ℤ) → ℂ) (p : ↥S → ℤ) (κ : ℂ) (α : Kˣ) : ℂ :=
  κ * A (ordVecS α - p) * ∏ v : ↥S, ((epsS v.1 (unitPartS v α) : ℂˣ) : ℂ)

private def coeffAd (Ad : (↥S → ℤ) → ℂ) (r : ↥S → ℤ) (α : Kˣ) : ℂ :=
  Ad (ordVecS α - r) * ∏ v : ↥S,
    (((localChar ω v.1 (uniformizerUnit K v.1) : ℂˣ) : ℂ) ^ (ordVecS α v) *
      ((localChar ω v.1 (unitPartS v α) : ℂˣ) : ℂ) * (((epsS v.1 (unitPartS v α))⁻¹ : ℂˣ) : ℂ))

private theorem coeffA_mul (A : (↥S → ℤ) → ℂ) (p : ↥S → ℤ) (κ : ℂ) (α β : Kˣ) (hβ : IsSUnit K S β) :
    coeffA epsS A p κ (α * β) =
      (∏ v : ↥S, ((epsS v.1 (localOf K v.1 β) : ℂˣ) : ℂ)) * coeffA epsS A p κ α := by
  simp only [coeffA, ordVecS_mul_of_isSUnit α β hβ, unitPartS_mul_of_isSUnit _ α β hβ, map_mul,
    Units.val_mul, Finset.prod_mul_distrib]
  ring

private theorem coeffAd_mul (Ad : (↥S → ℤ) → ℂ) (r : ↥S → ℤ) (α β : Kˣ) (hβ : IsSUnit K S β) :
    coeffAd epsS ω Ad r (α * β) =
      (∏ v : ↥S, ((localChar ω v.1 (localOf K v.1 β) : ℂˣ) : ℂ) * (((epsS v.1 (localOf K v.1 β))⁻¹ : ℂˣ) : ℂ))
        * coeffAd epsS ω Ad r α := by
  simp only [coeffAd, ordVecS_mul_of_isSUnit α β hβ, unitPartS_mul_of_isSUnit _ α β hβ, map_mul, mul_inv,
    Units.val_mul, Finset.prod_mul_distrib]
  ring

end Families

private def shiftDatum (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (m : ↥S → ℕ) (hm : ∀ v, 1 ≤ m v)
    (hε : ∀ (v : ↥S) (u : (v.1.adicCompletion K)ˣ), Valued.v (u : v.1.adicCompletion K) = 1 →
      IsOneMod K v.1 (m v) u → epsS v.1 u = 1)
    (hωl : ∀ (v : ↥S) (u : (v.1.adicCompletion K)ˣ), Valued.v (u : v.1.adicCompletion K) = 1 →
      IsOneMod K v.1 (m v) u → localChar ω v.1 u = 1)
    (Aelt : Kˣ)
    (hA : ∀ v : ↥S,
      Valued.v ((localOf K v.1 Aelt : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) = WithZero.exp (-(m v : ℤ)))
    (A Ad : (↥S → ℤ) → ℂ) (p r : ↥S → ℤ) (κ : ℂ)
    (hbdd : ∃ C : ℝ, ∀ α, ‖coeffA epsS A p κ α‖ ≤ C ∧ ‖coeffAd epsS ω Ad r α‖ ≤ C)
    (hfloor : ∀ α : Kˣ,
      (∃ v : ↥S, ¬ Valued.v (((localOf K v.1 α : (v.1.adicCompletion K)ˣ)) : v.1.adicCompletion K)
        ≤ WithZero.exp (addCharLevel (psiLocal K v.1))) →
      coeffA epsS A p κ α = 0 ∧ coeffAd epsS ω Ad r α = 0)
    (hne : ∃ α, coeffA epsS A p κ α ≠ 0) : JLData K S epsS ω where
  m := m
  m_pos := hm
  epsS_level := hε
  central_level := hωl
  A := Aelt
  A_ord := hA
  a := coeffA epsS A p κ
  ad := coeffAd epsS ω Ad r
  bounded := hbdd
  a_mul := fun α β hβ => coeffA_mul epsS A p κ α β hβ
  ad_mul := fun α β hβ => coeffAd_mul epsS ω Ad r α β hβ
  floor := hfloor
  a_ne_zero := hne

private def twistBase (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : ↥S) (s : ℂ) : ℂ :=
  ((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)

private theorem localChar_uniformizerUnit (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : ↥S) :
    localChar μ v.1 (uniformizerUnit K v.1) = μ (uniformizerIdele K v.1) := by
  unfold localChar uniformizerIdele
  rfl

private theorem localChar_mul_inv_apply (ω μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : ↥S)
    (x : (v.1.adicCompletion K)ˣ) : localChar (ω * μ)⁻¹ v.1 x = (localChar ω v.1 x * localChar μ v.1 x)⁻¹ := by
  simp only [localChar, MonoidHom.comp_apply, MonoidHom.inv_apply, MonoidHom.mul_apply]

private theorem coeffA_mul_sWeight (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (A : (↥S → ℤ) → ℂ) (p : ↥S → ℤ) (κ : ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμS : ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      localChar μ v u * epsS v u = 1)
    (R : SOrderReps K S) (n : ↥S → ℤ) (s : ℂ) :
    coeffA epsS A p κ (R.rep n) * sWeight K S μ (R.rep n) s =
      κ * A (n - p) * ∏ v : ↥S, twistBase μ v s ^ (n v) := by
  have hord : ordVecS (R.rep n) = n := ordVecS_rep R n
  have hv : ∀ v : ↥S,
      ((epsS v.1 (unitPartS v (R.rep n)) : ℂˣ) : ℂ) *
        (((localChar μ v.1 (localOf K v.1 (R.rep n)) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^
            (((WithZero.log (Valued.v (((localOf K v.1 (R.rep n) : (v.1.adicCompletion K)ˣ)) :
              v.1.adicCompletion K)) : ℤ) : ℂ) * (s - 1 / 2))) = twistBase μ v s ^ (n v) := by
    intro v
    have hlog : WithZero.log (Valued.v (((localOf K v.1 (R.rep n) : (v.1.adicCompletion K)ˣ)) :
        v.1.adicCompletion K)) = -(n v) := by
      rw [R.rep_ord n v, WithZero.log_exp]
    have hunit := hμS v.1 v.2 (unitPartS v (R.rep n)) (v_unitPartS v (R.rep n))
    have hunit' : ((localChar μ v.1 (unitPartS v (R.rep n)) : ℂˣ) : ℂ) *
        ((epsS v.1 (unitPartS v (R.rep n)) : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, hunit, Units.val_one]
    have hloc : localChar μ v.1 (localOf K v.1 (R.rep n)) =
        localChar μ v.1 (unitPartS v (R.rep n)) * μ (uniformizerIdele K v.1) ^ (n v) := by
      rw [localOf_eq_unitPartS_mul v (R.rep n), hord, map_mul, map_zpow, localChar_uniformizerUnit]
    have hq : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((((-(n v) : ℤ)) : ℂ) * (s - 1 / 2)) =
        (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v) := by
      rw [← Complex.cpow_int_mul]
      congr 1
      push_cast
      ring
    rw [hlog, hloc, hq, Units.val_mul, Units.val_zpow_eq_zpow_val, twistBase, mul_zpow]
    linear_combination (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) ^ (n v) *
      (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v)) * hunit'
  simp only [coeffA, sWeight, hord]
  rw [mul_assoc (κ * A (n - p)), ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun v _ => hv v

private theorem coeffAd_mul_sWeight (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (Ad : (↥S → ℤ) → ℂ) (r : ↥S → ℤ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμS : ∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      localChar μ v u * epsS v u = 1)
    (R : SOrderReps K S) (n : ↥S → ℤ) (s : ℂ) :
    coeffAd epsS ω Ad r (R.rep n) * sWeight K S (ω * μ)⁻¹ (R.rep n) s =
      Ad (n - r) * ∏ v : ↥S, twistBase μ⁻¹ v s ^ (n v) := by
  have hord : ordVecS (R.rep n) = n := ordVecS_rep R n
  have hv : ∀ v : ↥S,
      (((localChar ω v.1 (uniformizerUnit K v.1) : ℂˣ) : ℂ) ^ (n v) *
          ((localChar ω v.1 (unitPartS v (R.rep n)) : ℂˣ) : ℂ) *
          (((epsS v.1 (unitPartS v (R.rep n)))⁻¹ : ℂˣ) : ℂ)) *
        (((localChar (ω * μ)⁻¹ v.1 (localOf K v.1 (R.rep n)) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^
            (((WithZero.log (Valued.v (((localOf K v.1 (R.rep n) : (v.1.adicCompletion K)ˣ)) :
              v.1.adicCompletion K)) : ℤ) : ℂ) * (s - 1 / 2))) = twistBase μ⁻¹ v s ^ (n v) := by
    intro v
    have hlog : WithZero.log (Valued.v (((localOf K v.1 (R.rep n) : (v.1.adicCompletion K)ˣ)) :
        v.1.adicCompletion K)) = -(n v) := by
      rw [R.rep_ord n v, WithZero.log_exp]
    have hunit := hμS v.1 v.2 (unitPartS v (R.rep n)) (v_unitPartS v (R.rep n))
    have hunit' : ((localChar μ v.1 (unitPartS v (R.rep n)) : ℂˣ) : ℂ) *
        ((epsS v.1 (unitPartS v (R.rep n)) : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, hunit, Units.val_one]
    have hloc : localChar (ω * μ)⁻¹ v.1 (localOf K v.1 (R.rep n)) =
        ((localChar ω v.1 (unitPartS v (R.rep n)) * localChar ω v.1 (uniformizerUnit K v.1) ^ (n v)) *
          (localChar μ v.1 (unitPartS v (R.rep n)) * μ (uniformizerIdele K v.1) ^ (n v)))⁻¹ := by
      rw [localOf_eq_unitPartS_mul v (R.rep n), hord, localChar_mul_inv_apply, map_mul, map_zpow, map_mul,
        map_zpow, localChar_uniformizerUnit μ]
    have hq : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((((-(n v) : ℤ)) : ℂ) * (s - 1 / 2)) =
        (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (n v) := by
      rw [← Complex.cpow_int_mul]
      congr 1
      push_cast
      ring
    have hq0 : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl (Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr v.1.ne_bot))
    rw [hlog, hloc, hq, twistBase, MonoidHom.inv_apply]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, mul_zpow, inv_zpow']
    set Q : ℂ := ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) with hQdef
    have h1 := (localChar ω v.1 (uniformizerUnit K v.1)).ne_zero
    have h2 := (localChar ω v.1 (unitPartS v (R.rep n))).ne_zero
    have h3 := (epsS v.1 (unitPartS v (R.rep n))).ne_zero
    have h4 := (localChar μ v.1 (unitPartS v (R.rep n))).ne_zero
    have h5 := (μ (uniformizerIdele K v.1)).ne_zero
    have hPP : ((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) ^ (n v) * ((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) ^ (-n v)
        = 1 := by
      rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ h5)]
    field_simp
    linear_combination (-(((epsS v.1 (unitPartS v (R.rep n)) : ℂˣ) : ℂ) *
      ((localChar μ v.1 (unitPartS v (R.rep n)) : ℂˣ) : ℂ))) * hPP - hunit'
  simp only [coeffAd, sWeight, hord]
  rw [mul_assoc (Ad (n - r)), ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun v _ => hv v

private theorem tsum_twistBase_eq_sPart (A : (↥S → ℤ) → ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) :
    ∑' n : ↥S → ℤ, A n * ∏ v : ↥S, twistBase μ v s ^ (n v) = sPart K S A μ s := by
  simp only [sPart, twistBase]

private theorem apply_eq_one_of_hasConductorExponentAt {v : HeightOneSpectrum (𝓞 K)}
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c m : ℕ} (hc : HasConductorExponentAt K v χ c) (hcm : c ≤ m)
    (u : (v.adicCompletion K)ˣ) (hu : Valued.v (u : v.adicCompletion K) = 1) (h1 : IsOneMod K v m u) :
    χ u = 1 :=
  hc.1 u ⟨hu, Or.inr (le_trans h1 (WithZero.exp_le_exp.mpr (by omega)))⟩

private theorem isClosed_sphere_one (v : HeightOneSpectrum (𝓞 K)) :
    IsClosed {x : v.adicCompletion K | Valued.v x = 1} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hy
  by_cases hy0 : y = 0
  · subst hy0
    refine Filter.mem_of_superset (NumberField.AdelicBox.ball_mem_nhds (𝓞 K) K v 0 1 one_ne_zero) fun z hz => ?_
    simp only [Set.mem_setOf_eq, sub_zero, map_one] at hz
    exact ne_of_lt hz
  · refine Filter.mem_of_superset (NumberField.AdelicBox.ball_mem_nhds (𝓞 K) K v y y hy0) fun z hz => ?_
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff] at hz ⊢
    rw [Valuation.map_eq_of_sub_lt _ hz]
    exact hy

private theorem isCompact_sphere_one (v : HeightOneSpectrum (𝓞 K)) :
    IsCompact {x : v.adicCompletion K | Valued.v x = 1} := by
  have hO : IsCompact ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (v.adicCompletionIntegers K)))
  refine hO.of_isClosed_subset (isClosed_sphere_one v) fun x hx => ?_
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact le_of_eq hx

private theorem norm_epsS_apply (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (hepsS : ∀ v ∈ S, Continuous ⇑(epsS v)) (v : ↥S) (u : (v.1.adicCompletion K)ˣ)
    (hu : Valued.v (u : v.1.adicCompletion K) = 1) : ‖((epsS v.1 u : ℂˣ) : ℂ)‖ = 1 :=
  norm_apply_eq_one_of_continuous (isCompact_sphere_one v.1) (epsS v.1) (hepsS v.1 v.2) u hu

private theorem norm_localChar_apply (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) : ‖((localChar ω v x : ℂˣ) : ℂ)‖ = 1 :=
  hω.2.2 _

private theorem norm_coeffA_le (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (hepsS : ∀ v ∈ S, Continuous ⇑(epsS v)) (A : (↥S → ℤ) → ℂ) (p : ↥S → ℤ) (κ : ℂ) {C : ℝ}
    (hC : ∀ n, ‖A n‖ ≤ C) (α : Kˣ) : ‖coeffA epsS A p κ α‖ ≤ ‖κ‖ * C := by
  rw [coeffA, norm_mul, norm_mul, norm_prod, Finset.prod_eq_one fun v _ =>
    norm_epsS_apply epsS hepsS v _ (v_unitPartS v α), mul_one]
  exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg κ)

private theorem norm_coeffAd_le (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (hepsS : ∀ v ∈ S, Continuous ⇑(epsS v)) (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω)
    (Ad : (↥S → ℤ) → ℂ) (r : ↥S → ℤ) {C : ℝ} (hC : ∀ n, ‖Ad n‖ ≤ C) (α : Kˣ) :
    ‖coeffAd epsS ω Ad r α‖ ≤ C := by
  rw [coeffAd, norm_mul, norm_prod, Finset.prod_eq_one, mul_one]
  · exact hC _
  · intro v _
    rw [norm_mul, norm_mul, norm_zpow, norm_localChar_apply ω hω, norm_localChar_apply ω hω, one_zpow, one_mul,
      one_mul, Units.val_inv_eq_inv_val, norm_inv, norm_epsS_apply epsS hepsS v _ (v_unitPartS v α), inv_one]

private theorem ordVecS_lt_of_not_le {α : Kˣ} {v : ↥S} {ℓ : ℤ}
    (h : ¬ Valued.v ((localOf K v.1 α : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) ≤ WithZero.exp ℓ) :
    ordVecS α v < -ℓ := by
  rw [not_le, v_eq_exp_neg_valOrd (localOf K v.1 α), WithZero.exp_lt_exp] at h
  show valOrd (localOf K v.1 α) < -ℓ
  omega

private theorem summable_prod_pow {ι : Type} [Fintype ι] (x : ι → ℝ) (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1) : Summable (fun k : ι → ℕ => ∏ i, x i ^ k i) := by
  revert x
  refine Finite.induction_empty_option
    (P := fun (α : Type) => ∀ [Fintype α] (x : α → ℝ), (∀ i, 0 ≤ x i) → (∀ i, x i < 1) →
      Summable (fun k : α → ℕ => ∏ i, x i ^ k i)) ?_ ?_ ?_ ι
  · intro α β e h instβ x hx0 hx1
    letI : Fintype α := Fintype.ofEquiv β e.symm
    have hα := h (x ∘ e) (fun i => hx0 (e i)) (fun i => hx1 (e i))
    have heq : (fun k : β → ℕ => ∏ j, x j ^ k j) =
        (fun k : α → ℕ => ∏ i, (x ∘ e) i ^ k i) ∘ (fun k : β → ℕ => k ∘ e) := by
      funext k
      simp only [Function.comp_apply]
      exact (Fintype.prod_equiv e (fun i => x (e i) ^ k (e i)) (fun j => x j ^ k j) fun _ => rfl).symm
    rw [heq]
    refine hα.comp_injective fun k k' hk => ?_
    funext j
    simpa using congrFun hk (e.symm j)
  · intro inst x _ _
    exact Summable.of_finite
  · intro α instα h instOα x hx0 hx1
    obtain rfl : instOα = instFintypeOption := Subsingleton.elim _ _
    have hIH := h (fun i => x (some i)) (fun i => hx0 _) (fun i => hx1 _)
    have hgeo := summable_geometric_of_lt_one (hx0 none) (hx1 none)
    have hprod : Summable (fun q : ℕ × (α → ℕ) => x none ^ q.1 * ∏ i, x (some i) ^ q.2 i) := by
      refine summable_mul_of_summable_norm (f := fun m : ℕ => x none ^ m)
        (g := fun k : α → ℕ => ∏ i, x (some i) ^ k i) ?_ ?_
      · simpa only [Real.norm_of_nonneg (pow_nonneg (hx0 none) _)] using hgeo
      · simpa only [Real.norm_of_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (hx0 (some i)) _)] using hIH
    have heq : (fun k : Option α → ℕ => ∏ o, x o ^ k o) =
        (fun q : ℕ × (α → ℕ) => x none ^ q.1 * ∏ i, x (some i) ^ q.2 i) ∘
          (fun k : Option α → ℕ => (k none, fun i => k (some i))) := by
      funext k
      rw [Function.comp_apply, Fintype.prod_option]
    rw [heq]
    refine hprod.comp_injective fun k k' hk => ?_
    funext o
    cases o with
    | none => exact congrArg Prod.fst hk
    | some i => exact congrFun (congrArg Prod.snd hk) i

private theorem summable_of_orthant {ι : Type} [Fintype ι] (f : (ι → ℤ) → ℂ) (N : ι → ℤ) (C : ℝ) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1) (hzero : ∀ n, (∃ i, n i < N i) → f n = 0)
    (hbound : ∀ k : ι → ℕ, ‖f (fun i => N i + k i)‖ ≤ C * ∏ i, x i ^ k i) : Summable f := by
  set emb : (ι → ℕ) → (ι → ℤ) := fun k i => N i + k i with hemb
  have hinj : Function.Injective emb := by
    intro k k' h
    funext i
    have := congrFun h i
    simp only [hemb] at this
    exact_mod_cast (add_left_cancel this)
  have hrange : ∀ n ∉ Set.range emb, f n = 0 := by
    intro n hn
    apply hzero
    by_contra h
    simp only [not_exists, not_lt] at h
    exact hn ⟨fun i => (n i - N i).toNat, funext fun i => by simp [hemb, Int.toNat_of_nonneg (sub_nonneg.mpr (h i))]⟩
  rw [← hinj.summable_iff hrange]
  exact Summable.of_norm_bounded ((summable_prod_pow x hx0 hx1).mul_left C) fun k => hbound k

omit [NumberField K] in

private theorem summable_shift_prod (B : (↥S → ℤ) → ℂ) {C : ℝ} (hB : ∀ n, ‖B n‖ ≤ C) (n₀ k : ↥S → ℤ)
    (hB0 : ∀ n, (∃ v, n v < n₀ v) → B n = 0) (x : ↥S → ℂ) (hx0 : ∀ v, x v ≠ 0) (hx1 : ∀ v, ‖x v‖ < 1) :
    Summable (fun n : ↥S → ℤ => B (n - k) * ∏ v, x v ^ (n v)) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hB 0)
  refine summable_of_orthant _ (n₀ + k) (C * ∏ v, ‖x v‖ ^ ((n₀ + k) v)) (fun v => ‖x v‖)
    (fun v => norm_nonneg _) hx1 ?_ ?_
  · rintro n ⟨v, hv⟩
    rw [hB0 (n - k) ⟨v, ?_⟩, zero_mul]
    have := hv
    simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
    omega
  · intro j
    rw [norm_mul, norm_prod, mul_assoc, ← Finset.prod_mul_distrib]
    refine mul_le_mul (hB _) (le_of_eq (Finset.prod_congr rfl fun v _ => ?_))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _) hC0
    rw [norm_zpow, zpow_add₀ (norm_ne_zero_iff.mpr (hx0 v)), zpow_natCast]

private theorem absNorm_place_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < Ideal.absNorm v.asIdeal :=
  Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)

private theorem twistBase_ne_zero (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : ↥S) (s : ℂ) : twistBase μ v s ≠ 0 := by
  refine mul_ne_zero (Units.ne_zero _) ?_
  rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
  exact Or.inl (Nat.cast_ne_zero.mpr (absNorm_place_pos v.1).ne')

private theorem norm_twistBase (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : ↥S)
    (hμ1 : ‖((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ)‖ = 1) (s : ℂ) :
    ‖twistBase μ v s‖ = (Ideal.absNorm v.1.asIdeal : ℝ) ^ (1 / 2 - s.re) := by
  rw [twistBase, norm_mul, hμ1, one_mul, Complex.norm_natCast_cpow_of_pos (absNorm_place_pos v.1)]
  congr 1
  simp [Complex.sub_re]

private theorem norm_twistBase_lt_one (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : ↥S)
    (hμ1 : ‖((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ)‖ = 1) {s : ℂ} (hs : 1 < s.re) : ‖twistBase μ v s‖ < 1 := by
  rw [norm_twistBase μ v hμ1]
  exact Real.rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.mpr (NumberField.HeightOneSpectrum.one_lt_absNorm v.1))
    (by linarith)

private theorem differentiable_twistProd (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (k : ↥S → ℤ) :
    Differentiable ℂ fun s => ∏ v : ↥S, twistBase μ v s ^ k v := by
  refine Differentiable.fun_finsetProd fun v _ => ?_
  refine Differentiable.zpow ?_ (Or.inl (twistBase_ne_zero μ v))
  exact (differentiable_const _).mul (((differentiable_const _).sub differentiable_id).const_cpow
    (Or.inl (Nat.cast_ne_zero.mpr (absNorm_place_pos v.1).ne')))

private theorem exists_bound_twistProd (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hμ1 : ∀ v : ↥S, ‖((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ)‖ = 1) (k : ↥S → ℤ) (hk : ∀ v, 0 ≤ k v)
    (a : ℝ) :
    ∃ M : ℝ, ∀ s : ℂ, a ≤ s.re → ‖∏ v : ↥S, twistBase μ v s ^ k v‖ ≤ M := by
  refine ⟨∏ v : ↥S, (max 1 ((Ideal.absNorm v.1.asIdeal : ℝ) ^ (1 / 2 - a))) ^ (k v).toNat, fun s hs => ?_⟩
  rw [norm_prod]
  refine Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => ?_
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (hk v)
  rw [hj, Int.toNat_natCast, zpow_natCast, norm_pow, norm_twistBase μ v (hμ1 v)]
  refine pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_ j
  exact (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (absNorm_place_pos v.1)) (by linarith)).trans
    (le_max_right _ _)

private theorem sFactor_place (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : ↥S) (u : (v.1.adicCompletion K)ˣ)
    (hunit : localChar μ v.1 u * epsS v.1 u = 1) (m : ℕ) (p r : ℤ) (hm : (m : ℤ) = p + r) (s : ℂ) :
    (((epsS v.1 u)⁻¹ : ℂˣ) : ℂ) * twistBase μ v s ^ p =
      ((localChar μ v.1 (u * uniformizerUnit K v.1 ^ (m : ℤ)) : ℂˣ) : ℂ) *
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(m : ℂ) * (s - 1 / 2)) * twistBase μ⁻¹ v (1 - s) ^ r := by
  have hq0 : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (absNorm_place_pos v.1).ne'
  have hunit' : ((localChar μ v.1 u : ℂˣ) : ℂ) * ((epsS v.1 u : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, hunit, Units.val_one]
  have heu : (((epsS v.1 u)⁻¹ : ℂˣ) : ℂ) = ((localChar μ v.1 u : ℂˣ) : ℂ) := by
    rw [Units.val_inv_eq_inv_val]
    exact (eq_inv_of_mul_eq_one_left hunit').symm
  have hP0 := (μ (uniformizerIdele K v.1)).ne_zero
  rw [heu, map_mul, map_zpow, localChar_uniformizerUnit μ, twistBase, twistBase, MonoidHom.inv_apply,
    Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]
  set Q : ℂ := ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) with hQdef
  have hQ0 : Q ≠ 0 := by
    rw [hQdef, Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hq0
  have hqm : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(m : ℂ) * (s - 1 / 2)) = Q ^ (m : ℤ) := by
    rw [hQdef, ← Complex.cpow_int_mul]
    congr 1
    push_cast
    ring
  have hq1 : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - (1 - s)) = Q⁻¹ := by
    rw [hQdef, ← Complex.cpow_neg]
    congr 1
    ring
  rw [hqm, hq1, hm, zpow_add₀ hP0, zpow_add₀ hQ0, mul_zpow, mul_zpow, inv_zpow, inv_zpow]
  field_simp

end LanglandsTunnell.Converse.ShiftedFamily

open LanglandsTunnell.Converse.ShiftedFamily in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ)
    (hepsS : ∀ v ∈ S, Continuous ⇑(epsS v))
    (A Ad : (↥S → ℤ) → ℂ)
    (hbd : ∃ C : ℝ, ∀ n : ↥S → ℤ, ‖A n‖ ≤ C ∧ ‖Ad n‖ ≤ C)
    (hsupp : ∃ n₀ : ↥S → ℤ, ∀ n : ↥S → ℤ, (∃ v, n v < n₀ v) → A n = 0 ∧ Ad n = 0)
    (hA0 : A ≠ 0)
    (hnice : ∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, IsAdmissibleTwist K μ →
      (∀ v ∈ S, ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
        localChar μ v u * epsS v u = 1) →
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ)
        (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ)
        (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        IsNicePinned (twistedDatum K Pi S archR archC μ uR aR uC kC)
          (sPart K S A μ) (sPartDual K S Ad μ)
          (pinnedRootNumber K Pi μ S archR archC uR aR uC kC) (finiteConductor K μ S))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hω : IsAdmissibleTwist K ω) :
    ∃ d : JLData K S epsS ω, IsJLNice K S epsS ω d Pi archR archC := by
  classical

  choose cε hcε using fun v : ↥S =>
    exists_hasConductorExponentAt_of_continuous K v.1 (epsS v.1) (hepsS v.1 v.2)
  choose cω hcω using fun v : ↥S =>
    exists_hasConductorExponentAt_of_continuous K v.1 (localChar ω v.1) (continuous_localChar ω hω.2.1 v.1)
  obtain ⟨n₀, hn₀⟩ := hsupp
  obtain ⟨C, hC⟩ := hbd
  obtain ⟨R⟩ := nonempty_sOrderReps K S

  set ℓ : ↥S → ℤ := fun v => addCharLevel (psiLocal K v.1) with hℓ
  set P : ↥S → ℕ := fun v => (-ℓ v - n₀ v).toNat with hP
  set t : ↥S → ℕ := fun v => max 1 (max (cε v) (cω v)) with ht
  set m : ↥S → ℕ := fun v => P v + t v + P v with hm
  set p : ↥S → ℤ := fun v => (P v : ℤ) + (t v : ℤ) with hp
  set r : ↥S → ℤ := fun v => (P v : ℤ) with hr
  have hmpr : ∀ v, (m v : ℤ) = p v + r v := fun v => by
    simp only [hm, hp, hr]
    push_cast
    ring
  have hm1 : ∀ v, 1 ≤ m v := fun v => by
    have : 1 ≤ t v := le_max_left _ _
    simp only [hm]
    omega
  have hcεm : ∀ v, cε v ≤ m v := fun v => by
    have : cε v ≤ t v := (le_max_left _ _).trans (le_max_right _ _)
    simp only [hm]
    omega
  have hcωm : ∀ v, cω v ≤ m v := fun v => by
    have : cω v ≤ t v := (le_max_right _ _).trans (le_max_right _ _)
    simp only [hm]
    omega
  have hPℓ : ∀ v, -ℓ v - n₀ v ≤ (P v : ℤ) := fun v => Int.self_le_toNat _
  have hp0 : ∀ v, 0 ≤ p v := fun v => by simp only [hp]; positivity
  have hr0 : ∀ v, 0 ≤ r v := fun v => by simp only [hr]; positivity

  obtain ⟨α₀, hα₀, hα₀v⟩ := exists_ne_zero_valuation_eq_exp_neg K S (fun v => (m v : ℤ))
  set Aelt : Kˣ := Units.mk0 α₀ hα₀ with hAelt
  have hA : ∀ v : ↥S, Valued.v ((localOf K v.1 Aelt : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) =
      WithZero.exp (-(m v : ℤ)) := fun v => by
    rw [← hα₀v v]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 α₀
  have hAneg : ∀ v : ↥S, Valued.v ((localOf K v.1 (-Aelt) : (v.1.adicCompletion K)ˣ) : v.1.adicCompletion K) =
      WithZero.exp (-(m v : ℤ)) := fun v => by
    rw [← hA v]
    show Valued.v (algebraMap K (v.1.adicCompletion K) ((-Aelt : Kˣ) : K)) =
      Valued.v (algebraMap K (v.1.adicCompletion K) ((Aelt : Kˣ) : K))
    rw [Units.val_neg, map_neg, Valuation.map_neg]
  have hordA : ordVecS (S := S) (-Aelt) = fun v => (m v : ℤ) := (ordVecS_eq_iff _ _).mpr hAneg

  set κ : ℂ := ∏ v : ↥S, (((epsS v.1 (unitPartS v (-Aelt)))⁻¹ : ℂˣ) : ℂ) with hκ
  have hκ0 : κ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => Units.ne_zero _

  have hε : ∀ (v : ↥S) (u : (v.1.adicCompletion K)ˣ), Valued.v (u : v.1.adicCompletion K) = 1 →
      IsOneMod K v.1 (m v) u → epsS v.1 u = 1 := fun v u hu h1 =>
    apply_eq_one_of_hasConductorExponentAt (hcε v) (hcεm v) u hu h1
  have hωl : ∀ (v : ↥S) (u : (v.1.adicCompletion K)ˣ), Valued.v (u : v.1.adicCompletion K) = 1 →
      IsOneMod K v.1 (m v) u → localChar ω v.1 u = 1 := fun v u hu h1 =>
    apply_eq_one_of_hasConductorExponentAt (hcω v) (hcωm v) u hu h1
  have hbdd : ∃ C' : ℝ, ∀ α, ‖coeffA epsS A p κ α‖ ≤ C' ∧ ‖coeffAd epsS ω Ad r α‖ ≤ C' :=
    ⟨max (‖κ‖ * C) C, fun α =>
      ⟨(norm_coeffA_le epsS hepsS A p κ (fun n => (hC n).1) α).trans (le_max_left _ _),
        (norm_coeffAd_le epsS hepsS ω hω Ad r (fun n => (hC n).2) α).trans (le_max_right _ _)⟩⟩
  have hfloor : ∀ α : Kˣ,
      (∃ v : ↥S, ¬ Valued.v (((localOf K v.1 α : (v.1.adicCompletion K)ˣ)) : v.1.adicCompletion K)
        ≤ WithZero.exp (addCharLevel (psiLocal K v.1))) →
      coeffA epsS A p κ α = 0 ∧ coeffAd epsS ω Ad r α = 0 := by
    rintro α ⟨v, hv⟩
    have hlt : ordVecS α v < -ℓ v := ordVecS_lt_of_not_le hv
    have h1 : A (ordVecS α - p) = 0 :=
      (hn₀ _ ⟨v, by simp only [_root_.Pi.sub_apply]; have := hPℓ v; have := hp0 v; simp only [hp] at this ⊢; omega⟩).1
    have h2 : Ad (ordVecS α - r) = 0 :=
      (hn₀ _ ⟨v, by simp only [_root_.Pi.sub_apply]; have := hPℓ v; simp only [hr]; omega⟩).2
    simp only [coeffA, coeffAd, h1, h2, mul_zero, zero_mul, and_self]
  have hne : ∃ α, coeffA epsS A p κ α ≠ 0 := by
    obtain ⟨n, hn⟩ := Function.ne_iff.mp hA0
    refine ⟨R.rep (n + p), ?_⟩
    simp only [coeffA, ordVecS_rep, add_sub_cancel_right]
    exact mul_ne_zero (mul_ne_zero hκ0 hn) (Finset.prod_ne_zero_iff.mpr fun v _ => Units.ne_zero _)
  refine ⟨shiftDatum epsS ω m hm1 hε hωl Aelt hA A Ad p r κ hbdd hfloor hne, R,
    fun μ hμ uR aR uC kC hRc hCc => ?_⟩
  obtain ⟨hWF, hConv, -, Λ, Λd, hΛ, hΛd, hbΛ, hbΛd, hidΛ, hidΛd, hFE⟩ := hnice μ hμ.1 hμ.2 uR aR uC kC hRc hCc

  have hμ1 : ∀ v : ↥S, ‖((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ)‖ = 1 := fun v => hμ.1.2.2 _
  have hμ1' : ∀ v : ↥S, ‖((μ⁻¹ (uniformizerIdele K v.1) : ℂˣ) : ℂ)‖ = 1 := fun v => by
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hμ1 v, inv_one]
  set cS : ℂ → ℂ := fun s => κ * ∏ v : ↥S, twistBase μ v s ^ p v with hcS
  set cD : ℂ → ℂ := fun s => ∏ v : ↥S, twistBase μ⁻¹ v s ^ r v with hcD

  have hsum : ∀ s : ℂ, (shiftDatum epsS ω m hm1 hε hωl Aelt hA A Ad p r κ hbdd hfloor hne).sSum R μ s =
      cS s * sPart K S A μ s := fun s => by
    simp only [JLData.sSum, shiftDatum, hcS]
    rw [tsum_congr fun n => coeffA_mul_sWeight epsS A p κ μ hμ.2 R n s]
    simp_rw [mul_assoc κ]
    rw [tsum_mul_left, tsum_twistBase_eq_sPart, ← sPart_shift K S A μ s p]
    simp only [twistBase]
  have hsumD : ∀ s : ℂ, (shiftDatum epsS ω m hm1 hε hωl Aelt hA A Ad p r κ hbdd hfloor hne).sSumDual R μ s =
      cD s * sPartDual K S Ad μ s := fun s => by
    simp only [JLData.sSumDual, shiftDatum, hcD]
    rw [tsum_congr fun n => coeffAd_mul_sWeight epsS ω Ad r μ hμ.2 R n s, tsum_twistBase_eq_sPart,
      ← sPart_shift K S Ad μ⁻¹ s r, sPartDual_eq_sPart_inv]
    simp only [twistBase]

  have hfac : ∀ s : ℂ,
      cS s = (shiftDatum epsS ω m hm1 hε hωl Aelt hA A Ad p r κ hbdd hfloor hne).sFactor μ s * cD (1 - s) := by
    intro s
    simp only [hcS, hcD, JLData.sFactor, shiftDatum, hκ]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [localOf_eq_unitPartS_mul v (-Aelt), hordA]
    exact sFactor_place epsS μ v (unitPartS v (-Aelt)) (hμ.2 v.1 v.2 _ (v_unitPartS v (-Aelt))) (m v) (p v) (r v)
      (hmpr v) s
  refine ⟨hWF, hConv, 1, fun s => cS s * Λ s, fun s => cD s * Λd s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((differentiable_const κ).mul (differentiable_twistProd μ p)).mul hΛ
  · exact (differentiable_twistProd μ⁻¹ r).mul hΛd
  · intro a b
    obtain ⟨C₁, hC₁⟩ := hbΛ a b
    obtain ⟨M, hM⟩ := exists_bound_twistProd μ hμ1 p hp0 a
    refine ⟨‖κ‖ * M * C₁, fun s ha hb => ?_⟩
    rw [norm_mul, hcS, norm_mul]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM s ha)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hM s ha) (norm_nonneg κ)) (hC₁ s ha hb) (norm_nonneg _)
      (mul_nonneg (norm_nonneg κ) hM0)
  · intro a b
    obtain ⟨C₁, hC₁⟩ := hbΛd a b
    obtain ⟨M, hM⟩ := exists_bound_twistProd μ⁻¹ hμ1' r hr0 a
    refine ⟨M * C₁, fun s ha hb => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hM s ha) (hC₁ s ha hb) (norm_nonneg _) ((norm_nonneg _).trans (hM s ha))
  · intro s hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · have heq : (fun n : ↥S → ℤ => (shiftDatum epsS ω m hm1 hε hωl Aelt hA A Ad p r κ hbdd hfloor hne).a
          (R.rep n) * sWeight K S μ (R.rep n) s) = fun n => κ * (A (n - p) * ∏ v : ↥S, twistBase μ v s ^ (n v)) := by
        funext n
        rw [← mul_assoc]
        exact coeffA_mul_sWeight epsS A p κ μ hμ.2 R n s
      rw [heq]
      exact (summable_shift_prod A (fun n => (hC n).1) n₀ p (fun n hn => (hn₀ n hn).1) _
        (fun v => twistBase_ne_zero μ v s) fun v => norm_twistBase_lt_one μ v (hμ1 v) hs).mul_left κ
    · have heq : (fun n : ↥S → ℤ => (shiftDatum epsS ω m hm1 hε hωl Aelt hA A Ad p r κ hbdd hfloor hne).ad
          (R.rep n) * sWeight K S (ω * μ)⁻¹ (R.rep n) s) =
          fun n => Ad (n - r) * ∏ v : ↥S, twistBase μ⁻¹ v s ^ (n v) := by
        funext n
        exact coeffAd_mul_sWeight epsS ω Ad r μ hμ.2 R n s
      rw [heq]
      exact summable_shift_prod Ad (fun n => (hC n).2) n₀ r (fun n hn => (hn₀ n hn).2) _
        (fun v => twistBase_ne_zero μ⁻¹ v s) fun v => norm_twistBase_lt_one μ⁻¹ v (hμ1' v) hs
    · show cS s * Λ s = _
      rw [hsum s, hidΛ s hs]
      ring
    · show cD s * Λd s = _
      rw [hsumD s, hidΛd s hs]
      ring
  · intro s
    have hc : ((twistedDatum K Pi S archR archC μ uR aR uC kC).center : ℂ) = 1 / 2 := by
      show (((1 / 2 : ℝ)) : ℂ) = 1 / 2
      push_cast
      ring
    have hFE' := hFE s
    rw [hc] at hFE'
    show cS s * Λ s = _ * (cD (1 - s) * Λd (1 - s))
    rw [hFE', hfac s, show (2 : ℂ) * (1 / 2) - s = 1 - s by ring]
    ring

end

end S_LanglandsTunnell_Converse_exists_isJLNice_of_forall_isNicePinned
end P2MW
export P2MW.S_LanglandsTunnell_Converse_exists_isJLNice_of_forall_isNicePinned (solution)
