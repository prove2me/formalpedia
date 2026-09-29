-- Prove2me | solution 1 for ModularCurve.exists_mem_qExpFunctionFieldC_gamma0_and_eq_qExpand_of_qExpand_mul_coeffMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/2144b8cb-d379-55bb-af2f-247dfb560f22

import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mem_qExpFunctionFieldC_gamma0_and_eq_qExpand_of_qExpand_mul_coeffMap_eq
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open ModularCurve

namespace Decimation

section Ring

variable {R : Type*} [CommRing R] (N : ℕ) [NeZero N]

private theorem Npos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

private theorem bddBelow_support_decimate (r : ℤ) (f : LaurentSeries R) :
    BddBelow (Function.support fun m : ℤ => f.coeff (N * m + r)) := by
  by_cases hf : f = 0
  · refine ⟨0, fun m hm => ?_⟩
    exact absurd (by simp [hf]) hm
  · refine ⟨(f.order - r) / N, fun m hm => ?_⟩
    have h1 : f.order ≤ N * m + r := HahnSeries.order_le_of_coeff_ne_zero hm
    have h2 : (f.order - r) / N * N ≤ f.order - r := Int.ediv_mul_le _ (ne_of_gt (Npos N))
    have h3 : (f.order - r) / N * N ≤ m * N := by linarith [mul_comm (N : ℤ) m]
    exact le_of_mul_le_mul_right h3 (Npos N)

private noncomputable def decimate (r : ℤ) (f : LaurentSeries R) : LaurentSeries R :=
  HahnSeries.ofSuppBddBelow (fun m : ℤ => f.coeff (N * m + r)) (bddBelow_support_decimate N r f)

@[scoped simp] private theorem coeff_decimate (r : ℤ) (f : LaurentSeries R) (m : ℤ) :
    (decimate N r f).coeff m = f.coeff (N * m + r) := by
  rw [decimate, HahnSeries.coeff_ofSuppBddBelow]

private theorem coeffMap_decimate {S : Type*} [CommRing S] (φ : R →+* S) (r : ℤ) (f : LaurentSeries R) :
    coeffMap φ (decimate N r f) = decimate N r (coeffMap φ f) := by
  ext m
  rw [coeffMap_coeff, coeff_decimate, coeff_decimate, coeffMap_coeff]

private theorem coeffMap_qExpand {S : Type*} [CommRing S] (φ : R →+* S) (f : LaurentSeries R) :
    coeffMap φ (qExpand R N f) = qExpand S N (coeffMap φ f) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

private theorem coeff_sum_single_mul_qExpand (Z : ℕ → LaurentSeries R) (m : ℤ) (r₀ : ℕ) (hr₀ : r₀ < N) :
    (∑ r ∈ Finset.range N, HahnSeries.single (r : ℤ) (1 : R) * qExpand R N (Z r)).coeff ((N : ℤ) * m + r₀) =
      (Z r₀).coeff m := by
  rw [HahnSeries.coeff_sum]
  rw [Finset.sum_eq_single r₀]
  · rw [show (N : ℤ) * m + r₀ = (N : ℤ) * m + ((r₀ : ℕ) : ℤ) from rfl, HahnSeries.coeff_single_mul_add, one_mul,
      qExpand_coeff_mul]
  · intro r hr hne
    have hrN : r < N := Finset.mem_range.mp hr
    rw [show (N : ℤ) * m + r₀ = ((N : ℤ) * m + r₀ - r) + (r : ℤ) by ring, HahnSeries.coeff_single_mul_add, one_mul,
      qExpand_coeff_of_not_dvd]
    rintro ⟨c, hc⟩

    have h1 : (N : ℤ) ∣ (r₀ : ℤ) - r := ⟨c - m, by linarith⟩
    rcases h1 with ⟨d, hd⟩
    have hlt1 : ((r₀ : ℤ) - r) < N := by
      have : (r₀ : ℤ) < N := by exact_mod_cast hr₀
      linarith [show (0 : ℤ) ≤ r from by exact_mod_cast Nat.zero_le r]
    have hlt2 : -(N : ℤ) < (r₀ : ℤ) - r := by
      have : (r : ℤ) < N := by exact_mod_cast hrN
      linarith [show (0 : ℤ) ≤ r₀ from by exact_mod_cast Nat.zero_le r₀]
    have hd0 : d = 0 := by
      rw [hd] at hlt1 hlt2
      have hN := Npos N
      have : d < 1 := by
        by_contra hcon
        push_neg at hcon
        nlinarith
      have : -1 < d := by
        by_contra hcon
        push_neg at hcon
        nlinarith
      omega
    apply hne
    have : (r₀ : ℤ) = r := by rw [hd0, mul_zero] at hd; linarith
    exact_mod_cast this.symm
  · intro h
    exact absurd (Finset.mem_range.mpr hr₀) h

private theorem sum_single_mul_qExpand_decimate (f : LaurentSeries R) :
    ∑ r ∈ Finset.range N, HahnSeries.single (r : ℤ) (1 : R) * qExpand R N (decimate N r f) = f := by
  ext n
  have hN := Npos N
  set m := n / N with hm
  set r₀ := (n % N).toNat with hr₀
  have hr0 : 0 ≤ n % N := Int.emod_nonneg _ (ne_of_gt hN)
  have hrlt : n % N < N := Int.emod_lt_of_pos _ hN
  have hr₀Z : ((r₀ : ℕ) : ℤ) = n % N := by rw [hr₀, Int.toNat_of_nonneg hr0]
  have hr₀N : r₀ < N := by
    have : ((r₀ : ℕ) : ℤ) < N := by rw [hr₀Z]; exact hrlt
    exact_mod_cast this
  have hn : n = (N : ℤ) * m + r₀ := by rw [hr₀Z, hm]; exact (Int.mul_ediv_add_emod n N).symm
  rw [hn, coeff_sum_single_mul_qExpand N _ m r₀ hr₀N, coeff_decimate]

private theorem eq_of_sum_single_mul_qExpand_eq (Z W : ℕ → LaurentSeries R)
    (h : ∑ r ∈ Finset.range N, HahnSeries.single (r : ℤ) (1 : R) * qExpand R N (Z r) =
      ∑ r ∈ Finset.range N, HahnSeries.single (r : ℤ) (1 : R) * qExpand R N (W r))
    (r₀ : ℕ) (hr₀ : r₀ < N) : Z r₀ = W r₀ := by
  ext m
  rw [← coeff_sum_single_mul_qExpand N Z m r₀ hr₀, ← coeff_sum_single_mul_qExpand N W m r₀ hr₀, h]

end Ring

section Valuation

variable {L : Type*} [Field L] (A : ValuationSubring L) (N : ℕ) [NeZero N]

private theorem exists_mul_coeffMap_eq_of_qExpand_mul_coeffMap_eq (g : LaurentSeries L) (x y : LaurentSeries A)
    (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (h : qExpand L N g * coeffMap A.subtype y = coeffMap A.subtype x) :
    ∃ x' y' : LaurentSeries A, coeffMap (IsLocalRing.residue A) y' ≠ 0 ∧
      g * coeffMap A.subtype y' = coeffMap A.subtype x' := by
  have hN := Npos N

  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℤ, (coeffMap (IsLocalRing.residue A) y).coeff n₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hy (HahnSeries.ext (funext hcon))
  set r₀ := (n₀ % N).toNat with hr₀
  have hr0 : 0 ≤ n₀ % N := Int.emod_nonneg _ (ne_of_gt hN)
  have hr₀Z : ((r₀ : ℕ) : ℤ) = n₀ % N := by rw [hr₀, Int.toNat_of_nonneg hr0]
  have hr₀N : r₀ < N := by
    have : ((r₀ : ℕ) : ℤ) < N := by rw [hr₀Z]; exact Int.emod_lt_of_pos _ hN
    exact_mod_cast this
  have hdec : n₀ = (N : ℤ) * (n₀ / N) + r₀ := by rw [hr₀Z]; exact (Int.mul_ediv_add_emod n₀ N).symm
  refine ⟨decimate N r₀ x, decimate N r₀ y, ?_, ?_⟩
  ·
    intro h0
    apply hn₀
    have := congrArg (fun z : LaurentSeries (IsLocalRing.ResidueField A) => z.coeff (n₀ / N)) h0
    simp only [coeffMap_decimate, coeff_decimate, HahnSeries.coeff_zero] at this
    rwa [← hdec] at this
  ·
    have key := eq_of_sum_single_mul_qExpand_eq N
      (fun r => g * coeffMap A.subtype (decimate N r y)) (fun r => coeffMap A.subtype (decimate N r x)) ?_ r₀ hr₀N
    · exact key
    · have ey := sum_single_mul_qExpand_decimate N (coeffMap A.subtype y)
      have ex := sum_single_mul_qExpand_decimate N (coeffMap A.subtype x)
      calc ∑ r ∈ Finset.range N, HahnSeries.single (r : ℤ) (1 : L) *
              qExpand L N (g * coeffMap A.subtype (decimate N r y))
          = qExpand L N g * ∑ r ∈ Finset.range N, HahnSeries.single (r : ℤ) (1 : L) *
              qExpand L N (decimate N r (coeffMap A.subtype y)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [map_mul, coeffMap_decimate]; ring
        _ = coeffMap A.subtype x := by rw [ey, h]
        _ = ∑ r ∈ Finset.range N, HahnSeries.single (r : ℤ) (1 : L) *
              qExpand L N (coeffMap A.subtype (decimate N r x)) := by
            rw [← ex]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [coeffMap_decimate]

end Valuation

end Decimation
p2m_reactivate "P2MW.S_ModularCurve_exists_mem_qExpFunctionFieldC_gamma0_and_eq_qExpand_of_qExpand_mul_coeffMap_eq.Decimation"

namespace GaussB

open CongruenceSubgroup

private theorem T_mem_Gamma0 (M : ℕ) : ModularGroup.T ∈ Gamma0 M := by
  rw [Gamma0_mem]
  simp [ModularGroup.T]

private theorem qExpFunctionFieldC_gamma0_mul_le (q : ℕ) [Fact q.Prime] (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    (κ : Type*) [Field κ] [CharP κ q] :
    qExpFunctionFieldC κ (Gamma0 (q * N)) ≤ qExpFunctionFieldC κ (Gamma0 N) := by
  have hq : q.Prime := Fact.out
  have hq0 : 0 < q := hq.pos
  haveI : NeZero (q * N) := ⟨mul_ne_zero hq.ne_zero (NeZero.ne N)⟩
  have hpM : q ∣ q * N := dvd_mul_right q N
  have hpM2 : ¬ q ^ 2 ∣ q * N := by
    rintro ⟨c, hc⟩
    apply hqN
    refine ⟨c, mul_left_cancel₀ hq.ne_zero ?_⟩
    rw [pow_two, mul_assoc] at hc
    exact hc
  have h1 : qExpFunctionFieldC κ (Gamma0 (q * N)) ≤ qExpFunctionFieldC κ (CohCarrier.GammaH (q * N) ⊤) :=
    qExpFunctionFieldC_mono κ (CohCarrier.GammaH_le_Gamma0 ⊤)
  have h2 := ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup q (q * N) hpM hpM2 ⊤
    (fun u _ => Subgroup.mem_top u) κ
  have htop : ModularCurve.infSubgroup q (q * N) ⊤ hpM = ⊤ := by
    rw [ModularCurve.infSubgroup, Subgroup.map_top_of_surjective _ (ZMod.unitsMap_surjective _)]
  have hle : Gamma0 N ≤ CohCarrier.GammaH (q * N / q) (ModularCurve.infSubgroup q (q * N) ⊤ hpM) := by
    intro γ hγ
    rw [CohCarrier.mem_GammaH_iff]
    have hγ' : γ ∈ Gamma0 (q * N / q) := by rwa [Nat.mul_div_cancel_left N hq0]
    refine ⟨hγ', ?_⟩
    rw [htop]
    exact Subgroup.mem_top _
  have h3 : qExpFunctionFieldC κ (CohCarrier.GammaH (q * N / q) (ModularCurve.infSubgroup q (q * N) ⊤ hpM)) ≤
      qExpFunctionFieldC κ (Gamma0 N) := qExpFunctionFieldC_mono κ hle
  exact h1.trans (h2.trans h3)

end GaussB
p2m_reactivate "P2MW.S_ModularCurve_exists_mem_qExpFunctionFieldC_gamma0_and_eq_qExpand_of_qExpand_mul_coeffMap_eq.Decimation"

open Decimation GaussB CongruenceSubgroup in
theorem solution
    (q : ℕ) [Fact q.Prime] (N : ℕ) [NeZero N] (hqN : ¬ q ∣ N)
    {L : Type} [Field L] [Algebra ℚ L] (A : ValuationSubring L) [CharP (IsLocalRing.ResidueField A) q]
    (g : LaurentSeries L)
    (hg : g ∈ laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * N))))
    (x y : LaurentSeries A) (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (h : qExpand L q g * coeffMap A.subtype y = coeffMap A.subtype x)
    (r : LaurentSeries (IsLocalRing.ResidueField A))
    (hr : ∀ x' y' : LaurentSeries A, coeffMap (IsLocalRing.residue A) y' ≠ 0 →
      qExpand L q g * coeffMap A.subtype y' = coeffMap A.subtype x' →
        r * coeffMap (IsLocalRing.residue A) y' = coeffMap (IsLocalRing.residue A) x') :
    ∃ e : LaurentSeries (IsLocalRing.ResidueField A),
      e ∈ qExpFunctionFieldC (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma0 N) ∧
        r = qExpand (IsLocalRing.ResidueField A) q e := by
  classical
  set κ := IsLocalRing.ResidueField A

  obtain ⟨x₀, y₀, hy₀, hg₀⟩ := Decimation.exists_mul_coeffMap_eq_of_qExpand_mul_coeffMap_eq A q g x y hy h

  obtain ⟨R, hRg, hRres, -⟩ := ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div
    L A (Gamma0 (q * N)) (GaussB.T_mem_Gamma0 (q * N))
  have hgO : (⟨g, hg⟩ : laurentBaseChange L (qExpFunctionFieldC ℚ (Gamma0 (q * N)))) ∈ R.integers :=
    (hRg _).mpr ⟨x₀, y₀, hy₀, hg₀⟩
  set e : LaurentSeries κ :=
    ((R.residue ⟨_, hgO⟩ : qExpFunctionFieldC κ (Gamma0 (q * N))) : LaurentSeries κ) with he_def
  have he : e * coeffMap (IsLocalRing.residue A) y₀ = coeffMap (IsLocalRing.residue A) x₀ :=
    hRres ⟨_, hgO⟩ x₀ y₀ hy₀ hg₀

  have heN : e ∈ qExpFunctionFieldC κ (Gamma0 N) :=
    GaussB.qExpFunctionFieldC_gamma0_mul_le q N hqN κ (SetLike.coe_mem _)
  refine ⟨e, heN, ?_⟩

  have hy₀' : coeffMap (IsLocalRing.residue A) (qExpand A q y₀) ≠ 0 := by
    rw [Decimation.coeffMap_qExpand]
    intro h0
    exact hy₀ (qExpand_injective _ (by rw [h0, map_zero]))
  have hpres : qExpand L q g * coeffMap A.subtype (qExpand A q y₀) = coeffMap A.subtype (qExpand A q x₀) := by
    rw [Decimation.coeffMap_qExpand, Decimation.coeffMap_qExpand, ← map_mul, hg₀]
  have key := hr _ _ hy₀' hpres
  rw [Decimation.coeffMap_qExpand, Decimation.coeffMap_qExpand, ← he, map_mul] at key
  have hne : qExpand κ q (coeffMap (IsLocalRing.residue A) y₀) ≠ 0 := fun h0 =>
    hy₀ (qExpand_injective _ (by rw [h0, map_zero]))
  exact mul_right_cancel₀ hne key

end S_ModularCurve_exists_mem_qExpFunctionFieldC_gamma0_and_eq_qExpand_of_qExpand_mul_coeffMap_eq
end P2MW
export P2MW.S_ModularCurve_exists_mem_qExpFunctionFieldC_gamma0_and_eq_qExpand_of_qExpand_mul_coeffMap_eq (solution)
