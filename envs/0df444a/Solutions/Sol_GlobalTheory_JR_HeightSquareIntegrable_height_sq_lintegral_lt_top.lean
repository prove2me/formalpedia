-- Prove2me | solution 1 for GlobalTheory.JR.HeightSquareIntegrable.height_sq_lintegral_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:19.535166+00:00
-- url     : https://prove2.me/submissions/23a16acc-12f1-4c51-923e-e15b1e806df2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSubringEqOK
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralOrInvIsIntegralFiniteExtUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdempotentDecompositionOfIntegralityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHeightSqLintegralLtTop
import Theorems.Thm_P2M_GlobalTheory_JR_HeightSquareIntegrable_tsum_pi_prod_le__f38cf3f9f8ef
import Theorems.Thm_GlobalTheory_JR_HeightSquareIntegrable_eq_of_mul_eq
import Theorems.Thm_GlobalTheory_JR_HeightSquareIntegrable_mul_sum_eq
import Theorems.Thm_GlobalTheory_JR_HeightSquareIntegrable_mul_prod_eq
import Theorems.Thm_GlobalTheory_JR_Et_mem_OK_iff_isIntegral
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts
import Theorems.Thm_GlobalTheory_T_idempotent_decomposition_of_integrality
import Theorems.Thm_GlobalTheory_T_isIntegral_or_inv_isIntegral_finite_ext_ultrametric


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HeightSquareIntegrable
namespace GlobalTheory.JR.HeightSquareIntegrable
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.K), μ.IsAddHaarMeasure → ∫⁻ z, (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ < ⊤ := by
  intro F E _ _ _ _ hU A μ hμ
  classical
  haveI := hU.ultraF; haveI := hU.lcF; haveI := hU.charZero
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : IsTopologicalAddGroup A.K := IsModuleTopology.topologicalAddGroup F A.K
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  let b := Module.finBasis F A.K
  haveI : T2Space A.K := .of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  haveI : SecondCountableTopology A.K := b.equivFunL.toHomeomorph.secondCountableTopology
  obtain ⟨-, -, -, -, -, -, -, -, -, hOo, hOc, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  obtain ⟨m, f, hid, hor, hsum, hsc, hvp⟩ :=
    GlobalTheory.T.idempotent_decomposition_of_integrality F E A (fun k _ _ _ y hy => GlobalTheory.T.isIntegral_or_inv_isIntegral_finite_ext_ultrametric F k y hy)
  have hOR : ∀ x, x ∈ A.OK ↔ x ∈ R := fun x => by rw [← hR, SetLike.mem_coe]
  have hfR : ∀ i, f i ∈ R := fun i => by
    rw [← hOR, Et.mem_OK_iff_isIntegral]
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num), ?_⟩
    simp [sq, hid i]
  obtain ⟨π, hπ0, hπ1⟩ := NormedField.exists_norm_lt_one F
  have hπ : π ≠ 0 := norm_pos_iff.1 hπ0
  have hpp : algebraMap F A.K π * algebraMap F A.K π⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hπ, map_one]
  have hpR : algebraMap F A.K π ∈ R := by
    rw [← hOR, Et.mem_OK_iff_isIntegral]
    have hmem : π ∈ (NormedField.valuation (K := F)).integer := by
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply]; exact_mod_cast hπ1.le
    exact (isIntegral_algebraMap (R := (NormedField.valuation (K := F)).integer) (A := A.K) (x := ⟨π, hmem⟩) : _)
  set p := algebraMap F A.K π with hp
  set p' := algebraMap F A.K π⁻¹ with hp'
  let u : Fin m → A.Kˣ := fun i => ⟨f i * p + (1 - f i), f i * p' + (1 - f i),
    by linear_combination (f i * f i) * hpp + (2 - p - p') * hid i,
    by linear_combination (f i * f i) * hpp + (2 - p - p') * hid i⟩
  have hu : ∀ i, ((u i : A.Kˣ) : A.K) = f i * p + (1 - f i) := fun i => rfl
  have huR : ∀ i, ((u i : A.Kˣ) : A.K) ∈ R := fun i => by
    rw [hu]; exact R.add_mem (R.mul_mem (hfR i) hpR) (R.sub_mem R.one_mem (hfR i))
  haveI : μ.IsAddHaarMeasure := hμ
  have hμO0 : μ A.OK ≠ 0 := hOo.measure_ne_zero μ ⟨0, (hOR 0).2 R.zero_mem⟩
  have hμOt : μ A.OK ≠ ⊤ := hOc.measure_lt_top.ne
  have hsmulO : ∀ v : A.Kˣ, (v : A.K) ∈ R → v • A.OK ⊆ A.OK := by
    rintro v hv _ ⟨y, hy, rfl⟩
    rw [hOR] at hy ⊢
    exact R.mul_mem hv hy
  have hle1 : ∀ v : A.Kˣ, (v : A.K) ∈ R → distribHaarChar A.K v ≤ 1 := by
    intro v hv
    have h2 : μ (v • A.OK) ≤ μ A.OK := measure_mono (hsmulO v hv)
    rw [← distribHaarChar_mul μ] at h2
    have h3 : (distribHaarChar A.K v : ℝ≥0∞) ≤ 1 := by
      rwa [← ENNReal.mul_le_mul_iff_left hμO0 hμOt, one_mul]
    exact_mod_cast h3
  have hlt1 : ∀ i, distribHaarChar A.K (u i) < 1 := by
    intro i
    have hsub := hsmulO (u i) (huR i)
    have hcl : IsClosed ((u i) • A.OK) := (hOc.smul (u i)).isClosed
    have hfi : f i ∉ (u i) • A.OK := by
      rintro ⟨y, hy, hyf⟩
      have hyf' : ((u i : A.Kˣ) : A.K) * y = f i := hyf
      have hy' : y = p' * f i := by
        have h1 : y = (((u i)⁻¹ : A.Kˣ) : A.K) * f i := by rw [← hyf', Units.inv_mul_cancel_left]
        rw [h1]
        show (f i * p' + (1 - f i)) * f i = p' * f i
        linear_combination (p' - 1) * hid i
      have hn : 1 < ‖π⁻¹‖ := by rw [norm_inv]; exact (one_lt_inv₀ hπ0).2 hπ1
      exact hsc i π⁻¹ hn (hy' ▸ hy)
    have hopen : IsOpen (A.OK \ (u i) • A.OK) := hOo.sdiff hcl
    have hpos : μ (A.OK \ (u i) • A.OK) ≠ 0 := hopen.measure_ne_zero μ ⟨f i, (hOR _).2 (hfR i), hfi⟩
    have hadd : μ ((u i) • A.OK) + μ (A.OK \ (u i) • A.OK) = μ A.OK := by
      rw [measure_add_sdiff hcl.measurableSet.nullMeasurableSet, Set.union_eq_right.2 hsub]
    have hlt : μ ((u i) • A.OK) < μ A.OK := by
      rw [← hadd]; exact ENNReal.lt_add_right (ne_top_of_le_ne_top hμOt (measure_mono hsub)) hpos
    rw [← distribHaarChar_mul μ] at hlt
    have h4 : (distribHaarChar A.K (u i) : ℝ≥0∞) < 1 := by
      by_contra hc
      have hc' : 1 ≤ (distribHaarChar A.K (u i) : ℝ≥0∞) := not_lt.1 hc
      have h5 : 1 * μ A.OK ≤ (distribHaarChar A.K (u i) : ℝ≥0∞) * μ A.OK := by gcongr
      rw [one_mul] at h5; exact absurd hlt (not_lt.2 h5)
    exact_mod_cast h4
  have hex : ∀ z : A.K, ∀ i, ∃ n : ℕ, π ^ n • (f i * z) ∈ A.OK := by
    intro z i
    have ht : Tendsto (fun n : ℕ => π ^ n • (f i * z)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hπ1).smul_const (f i * z)
      simpa using this
    exact (ht.eventually (hOo.mem_nhds ((hOR 0).2 R.zero_mem))).exists

  let N : A.K → Fin m → ℕ := fun z i => Nat.find (hex z i)
  have hNspec : ∀ z i, π ^ N z i • (f i * z) ∈ A.OK := fun z i => Nat.find_spec (hex z i)
  have hNmin : ∀ z i, N z i ≠ 0 → π ^ (N z i - 1) • (f i * z) ∉ A.OK := fun z i hi =>
    Nat.find_min (hex z i) (Nat.sub_lt (Nat.pos_of_ne_zero hi) one_pos)
  have hsmul : ∀ (k : ℕ) (x : A.K), π ^ k • x = p ^ k * x := fun k x => by
    rw [Algebra.smul_def, map_pow]
  have hrep : ∀ x : A.K, x = ∑ j, f j * x := fun x => by rw [← Finset.sum_mul, hsum, one_mul]
  have hkey : ∀ z : A.K, ∃ s : A.Kˣ, ((s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧
      ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1) ∧
      distribHaarChar A.K s ≤ ∏ i, distribHaarChar A.K (u i) ^ (N z i - 1) := by
    intro z
    set n := N z with hn
    have hn0 : ∀ i, π ^ n i • (f i * z) ∈ A.OK := fun i => hNspec z i
    have hnmin : ∀ i, n i ≠ 0 → f i * (π ^ (n i - 1) • z) ∉ A.OK := fun i hi => by
      rw [mul_smul_comm]; exact hNmin z i hi
    have hw : ∀ i, ∃ w ∈ R, n i ≠ 0 → w * (f i * (π ^ (n i - 1) • z)) = f i := by
      intro i
      by_cases hi : n i = 0
      · exact ⟨0, R.zero_mem, fun h => absurd hi h⟩
      · obtain ⟨w, hwO, hw⟩ := hvp i _ (hnmin i hi)
        exact ⟨w, (hOR w).1 hwO, fun _ => hw⟩
    choose w hwR hwf using hw
    obtain ⟨a, ha⟩ : ∃ a : Fin m → A.K, ∀ i, a i = if n i = 0 then 1 else w i := ⟨_, fun i => rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : Fin m → A.K, ∀ i, c i = if n i = 0 then 1 else π ^ (n i - 1) • z :=
      ⟨_, fun i => rfl⟩
    have haR : ∀ i, a i ∈ R := fun i => by
      rw [ha]; split_ifs
      · exact R.one_mem
      · exact hwR i
    have hac : ∀ i, f i * (a i * c i) = f i := fun i => by
      rw [ha, hc]; split_ifs with hi
      · ring
      · linear_combination hwf i hi
    obtain ⟨σ, hσ⟩ : ∃ σ : A.K, σ = ∑ i, f i * a i := ⟨_, rfl⟩
    obtain ⟨σ', hσ'⟩ : ∃ σ' : A.K, σ' = ∑ i, f i * c i := ⟨_, rfl⟩
    have hfσ : ∀ j, f j * σ = f j * a j := fun j => by rw [hσ]; exact mul_sum_eq hid hor a j
    have hfσ' : ∀ j, f j * σ' = f j * c j := fun j => by rw [hσ']; exact mul_sum_eq hid hor c j
    have hσσ : σ * σ' = 1 := by
      refine eq_of_mul_eq hsum fun j => ?_
      calc f j * (σ * σ') = (f j * σ) * σ' := by ring
        _ = a j * (f j * σ') := by rw [hfσ]; ring
        _ = f j * (a j * c j) := by rw [hfσ']; ring
        _ = f j * 1 := by rw [hac, mul_one]
    let σU : A.Kˣ := ⟨σ, σ', hσσ, by rw [mul_comm]; exact hσσ⟩
    have hσR : σ ∈ R := by rw [hσ]; exact R.sum_mem fun i _ => R.mul_mem (hfR i) (haR i)
    let q : A.Kˣ := ∏ i, u i ^ (n i - 1)
    have hfq : ∀ j, f j * (q : A.K) = f j * p ^ (n j - 1) := fun j => by
      rw [Units.coe_prod]; simp only [Units.val_pow_eq_pow_val]
      exact mul_prod_eq hid hor (fun _ => p) (fun i => n i - 1) j
    have hqR : (q : A.K) ∈ R := by
      rw [Units.coe_prod]
      exact R.prod_mem fun i _ => by rw [Units.val_pow_eq_pow_val]; exact R.pow_mem (huR i) _
    have hsval : ((σU * q : A.Kˣ) : A.K) = σ * q := rfl
    have hfs : ∀ j, f j * ((σU * q : A.Kˣ) : A.K) = a j * (f j * p ^ (n j - 1)) := fun j => by
      rw [hsval, ← hfq]
      calc f j * (σ * q) = (f j * σ) * q := by ring
        _ = _ := by rw [hfσ]; ring
    have hfs0 : ∀ j, n j = 0 → f j * ((σU * q : A.Kˣ) : A.K) = f j := fun j hj => by
      rw [hfs, ha, if_pos hj, hj]; simp
    have hfsz : ∀ j, f j * (((σU * q : A.Kˣ) : A.K) * z) = if n j = 0 then f j * z else f j := by
      intro j
      rw [← mul_assoc, hfs]
      split_ifs with hj
      · rw [ha, if_pos hj, hj]; simp
      · have h1 := hwf j hj
        rw [hsmul] at h1
        rw [ha, if_neg hj]; linear_combination h1
    refine ⟨σU * q, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hOR, hsval]; exact R.mul_mem hσR hqR
    · rw [hOR, hrep (((σU * q : A.Kˣ) : A.K) * z)]
      refine R.sum_mem fun j _ => ?_
      rw [hfsz]; split_ifs with hj
      · have h1 := hn0 j; rw [hj, pow_zero, one_smul, hOR] at h1; exact h1
      · exact hfR j
    · refine ⟨∑ i, f i * (if n i = 0 then 1 else 0), ?_, ∑ i, f i * (if n i = 0 then 0 else 1), ?_,
        eq_of_mul_eq hsum fun j => ?_⟩
      · rw [hOR]; refine R.sum_mem fun i _ => R.mul_mem (hfR i) ?_
        split_ifs
        · exact R.one_mem
        · exact R.zero_mem
      · rw [hOR]; refine R.sum_mem fun i _ => R.mul_mem (hfR i) ?_
        split_ifs
        · exact R.zero_mem
        · exact R.one_mem
      · have e1 : ∀ (x y X Y : A.K), f j * (x * X + y * Y) = (f j * x) * X + (f j * y) * Y :=
          fun x y X Y => by ring
        rw [e1, mul_sum_eq hid hor, mul_sum_eq hid hor]
        split_ifs with hj
        · rw [mul_one, mul_zero, zero_mul, add_zero, hfs0 j hj]
        · rw [mul_zero, zero_mul, zero_add, mul_one, hfsz, if_neg hj]
    · rw [map_mul, map_prod]; simp only [map_pow]
      exact mul_le_of_le_one_left zero_le (hle1 σU hσR)

  set C : Fin m → ℝ≥0∞ := fun i => (distribHaarChar A.K (u i) : ℝ≥0∞) with hCdef
  set D : Fin m → ℝ≥0∞ := fun i => (distribHaarChar A.K (u i)⁻¹ : ℝ≥0∞) with hDdef
  have hCD : ∀ i, C i * D i = 1 := fun i => by
    simp only [hCdef, hDdef]
    rw [← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one]
  have hC1 : ∀ i, C i < 1 := fun i => ENNReal.coe_lt_one_iff.2 (hlt1 i)
  have hD1 : ∀ i, 1 ≤ D i := fun i => by
    calc (1 : ℝ≥0∞) = C i * D i := (hCD i).symm
      _ ≤ 1 * D i := by gcongr; exact (hC1 i).le
      _ = D i := one_mul _
  have hpow : ∀ i (k : ℕ), C i ^ (k - 1) ≤ D i * C i ^ k := fun i k => by
    cases k with
    | zero => simpa using hD1 i
    | succ k =>
      rw [Nat.add_sub_cancel, pow_succ, show D i * (C i ^ k * C i) = C i ^ k * (C i * D i) by ring,
        hCD, mul_one]
  let Q : (Fin m → ℕ) → A.Kˣ := fun k => ∏ i, u i ^ k i
  have hfQ : ∀ k j, f j * (Q k : A.K) = f j * p ^ k j := fun k j => by
    simp only [Q]; rw [Units.coe_prod]; simp only [Units.val_pow_eq_pow_val]
    exact mul_prod_eq hid hor (fun _ => p) k j
  let S : (Fin m → ℕ) → Set A.K := fun k => {z | (Q k : A.K) * z ∈ A.OK}
  have hzS : ∀ z, z ∈ S (N z) := fun z => by
    show (Q (N z) : A.K) * z ∈ A.OK
    rw [hOR, hrep ((Q (N z) : A.K) * z)]
    refine R.sum_mem fun j _ => ?_
    have h1 := hNspec z j
    rw [hsmul, hOR] at h1
    have e : f j * ((Q (N z) : A.K) * z) = p ^ N z j * (f j * z) := by
      rw [← mul_assoc, hfQ]; ring
    rw [e]; exact h1
  have hSm : ∀ k, MeasurableSet (S k) := fun k =>
    (hOo.preimage (continuous_const_mul _)).measurableSet
  have hμS : ∀ k, μ (S k) = (∏ i, D i ^ k i) * μ A.OK := fun k => by
    have hset : S k = (Q k)⁻¹ • A.OK := by
      ext z; rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def]; rfl
    have hinv : (Q k)⁻¹ = ∏ i, (u i)⁻¹ ^ k i := by
      simp only [Q, ← Finset.prod_inv_distrib, inv_pow]
    rw [hset, ← distribHaarChar_mul μ, hinv]
    simp only [hDdef, map_prod, map_pow, ENNReal.ofNNReal_finsetProd, ENNReal.coe_pow]
  refine lt_of_le_of_lt (lintegral_mono (g := fun z => ∑' k : Fin m → ℕ,
    (S k).indicator (fun _ => (∏ i, D i) ^ 2 * ∏ i, (C i ^ k i) ^ 2) z) fun z => ?_) ?_
  · obtain ⟨s, hs, hsle⟩ := hkey z
    have h1 : (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK,
        α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ≤ ∏ i, C i ^ (N z i - 1) := by
      refine (iInf₂_le s hs).trans ?_
      have e : A.absK (s : A.K) = distribHaarChar A.K s := by simp [Et.absK]
      rw [e, ENNReal.ofReal_coe_nnreal]
      simp only [hCdef]
      exact_mod_cast hsle
    have h2 : ∏ i, C i ^ (N z i - 1) ≤ (∏ i, D i) * ∏ i, C i ^ N z i := by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_le_prod' fun i _ => hpow i _
    refine le_trans ?_ (ENNReal.le_tsum (N z))
    rw [Set.indicator_of_mem (hzS z), Finset.prod_pow, ← mul_pow]
    exact pow_le_pow_left₀ zero_le (h1.trans h2) 2
  · rw [lintegral_tsum (fun k => (measurable_const.indicator (hSm k)).aemeasurable)]
    have hterm : ∀ k : Fin m → ℕ, ∫⁻ z, (S k).indicator (fun _ => (∏ i, D i) ^ 2 * ∏ i, (C i ^ k i) ^ 2) z ∂μ
        = ((∏ i, D i) ^ 2 * μ A.OK) * ∏ i, C i ^ k i := by
      intro k
      rw [lintegral_indicator_const (hSm k), hμS]
      have e : (∏ i, (C i ^ k i) ^ 2) * ∏ i, D i ^ k i = ∏ i, C i ^ k i := by
        rw [← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl fun i _ => ?_
        rw [sq, mul_assoc, ← mul_pow, hCD, one_pow, mul_one]
      calc _ = (∏ i, D i) ^ 2 * μ A.OK * ((∏ i, (C i ^ k i) ^ 2) * ∏ i, D i ^ k i) := by ring
        _ = _ := by rw [e]
    rw [tsum_congr hterm, ENNReal.tsum_mul_left]
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top
      (ENNReal.prod_lt_top fun i _ => ENNReal.coe_lt_top)) hμOt.lt_top) ?_
    refine lt_of_le_of_lt (tsum_pi_prod_le' (fun i (x : ℕ) => C i ^ x)) ?_
    refine ENNReal.prod_lt_top fun i _ => ?_
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt (hC1 i))
end GlobalTheory.JR.HeightSquareIntegrable
