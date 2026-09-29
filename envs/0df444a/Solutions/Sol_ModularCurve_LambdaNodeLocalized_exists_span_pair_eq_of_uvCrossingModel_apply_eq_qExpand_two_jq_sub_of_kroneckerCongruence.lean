-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.exists_span_pair_eq_of_uvCrossingModel_apply_eq_qExpand_two_jq_sub_of_kroneckerCongruence
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2dadbe3c-f26d-5b00-a075-b8dd32724e65

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_U_powerSeries
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_ringEquiv_quotient_span_V_powerSeries
import Theorems.Thm_ModularCurve_UVCrossingModel_maximalIdeal_eq_map_maximalIdeal_sup_span_pair
import Theorems.Thm_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_PowerSeries_quotient_span_X_sub_C_pow_of_irreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_exists_span_pair_eq_of_uvCrossingModel_apply_eq_qExpand_two_jq_sub_of_kroneckerCongruence

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "IsLocalRing ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_span_pair_eq_of_uvCrossingModel_apply_eq_qExpand_two_jq_sub_of_kroneckerCongruence.ModularCurve ModularCurve.UVCrossingModel"
open ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC qExpand ssJSet jWidth jWidth_pos UVCrossingModel UVCrossingModel.U UVCrossingModel.V UVCrossingModel.const UVCrossingModel.constHom UVCrossingModel.constHom_apply UVCrossingModel.exists_ringEquiv_quotient_span_U_powerSeries UVCrossingModel.exists_ringEquiv_quotient_span_V_powerSeries UVCrossingModel.maximalIdeal_eq_map_maximalIdeal_sup_span_pair UVCrossingModel.isLocalRing_of_not_isUnit NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace Ws30Pins

section Branch
variable {W : Type*} [CommRing W] (π p : W)

theorem exists_eq_C_mul_of_map_factor_eq_zero (h : Ideal.span {π} ≤ Ideal.span {p})
    (F : PowerSeries (W ⧸ Ideal.span {π})) (hF : PowerSeries.map (Ideal.Quotient.factor h) F = 0) :
    ∃ G : PowerSeries (W ⧸ Ideal.span {π}), F = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {π}) p) * G := by
  classical
  have hc : ∀ n, ∃ d : W, PowerSeries.coeff n F = Ideal.Quotient.mk (Ideal.span {π}) p * Ideal.Quotient.mk (Ideal.span {π}) d := by
    intro n
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (PowerSeries.coeff n F)
    have h0 : Ideal.Quotient.factor h (PowerSeries.coeff n F) = 0 := by
      rw [← PowerSeries.coeff_map, hF, map_zero]
    rw [← hw, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h0
    obtain ⟨d, hd⟩ := h0
    refine ⟨d, ?_⟩
    rw [← hw, ← hd, map_mul, mul_comm]
  choose d hd using hc
  refine ⟨PowerSeries.mk fun n => Ideal.Quotient.mk (Ideal.span {π}) (d n), PowerSeries.ext fun n => ?_⟩
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hd]

theorem exists_branchMapV (h : Ideal.span {π} ≤ Ideal.span {p}) :
    ∃ ρ : UVCrossingModel W π →+* PowerSeries (W ⧸ Ideal.span {p}),
      ρ (U π) = 0 ∧ ρ (V π) = PowerSeries.X ∧ (∀ w, ρ (const π w) = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {p}) w)) ∧
      ∀ z, ρ z = 0 → z ∈ Ideal.span {const π p, U π} := by
  obtain ⟨e, heV, heU, heC⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_U_powerSeries (W := W) π
  refine ⟨(PowerSeries.map (Ideal.Quotient.factor h)).comp (e.toRingHom.comp (Ideal.Quotient.mk _)), ?_, ?_, ?_, ?_⟩
  · show PowerSeries.map (Ideal.Quotient.factor h) (e (Ideal.Quotient.mk _ (U π))) = 0
    rw [heU, map_zero]
  · show PowerSeries.map (Ideal.Quotient.factor h) (e (Ideal.Quotient.mk _ (V π))) = PowerSeries.X
    rw [heV, PowerSeries.map_X]
  · intro w
    show PowerSeries.map (Ideal.Quotient.factor h) (e (Ideal.Quotient.mk _ (const π w))) = _
    rw [heC, PowerSeries.map_C, Ideal.Quotient.factor_mk]
  · intro z hz
    change PowerSeries.map (Ideal.Quotient.factor h) (e (Ideal.Quotient.mk _ z)) = 0 at hz
    obtain ⟨G, hG⟩ := exists_eq_C_mul_of_map_factor_eq_zero π p h _ hz
    obtain ⟨g', hg'⟩ := Ideal.Quotient.mk_surjective (e.symm G)
    have h1 : Ideal.Quotient.mk (Ideal.span {U π}) z = Ideal.Quotient.mk (Ideal.span {U π}) (const π p * g') := by
      apply e.injective
      rw [hG, map_mul (Ideal.Quotient.mk _), map_mul e, heC, hg', RingEquiv.apply_symm_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h1
    obtain ⟨b, hb⟩ := h1
    have : z = const π p * g' + b * U π := by rw [hb]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

theorem exists_branchMapU (h : Ideal.span {π} ≤ Ideal.span {p}) :
    ∃ ρ : UVCrossingModel W π →+* PowerSeries (W ⧸ Ideal.span {p}),
      ρ (V π) = 0 ∧ ρ (U π) = PowerSeries.X ∧ (∀ w, ρ (const π w) = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {p}) w)) ∧
      ∀ z, ρ z = 0 → z ∈ Ideal.span {const π p, V π} := by
  obtain ⟨e, heU, heV, heC⟩ := ModularCurve.UVCrossingModel.exists_ringEquiv_quotient_span_V_powerSeries (W := W) π
  refine ⟨(PowerSeries.map (Ideal.Quotient.factor h)).comp (e.toRingHom.comp (Ideal.Quotient.mk _)), ?_, ?_, ?_, ?_⟩
  · show PowerSeries.map (Ideal.Quotient.factor h) (e (Ideal.Quotient.mk _ (V π))) = 0
    rw [heV, map_zero]
  · show PowerSeries.map (Ideal.Quotient.factor h) (e (Ideal.Quotient.mk _ (U π))) = PowerSeries.X
    rw [heU, PowerSeries.map_X]
  · intro w
    show PowerSeries.map (Ideal.Quotient.factor h) (e (Ideal.Quotient.mk _ (const π w))) = _
    rw [heC, PowerSeries.map_C, Ideal.Quotient.factor_mk]
  · intro z hz
    change PowerSeries.map (Ideal.Quotient.factor h) (e (Ideal.Quotient.mk _ z)) = 0 at hz
    obtain ⟨G, hG⟩ := exists_eq_C_mul_of_map_factor_eq_zero π p h _ hz
    obtain ⟨g', hg'⟩ := Ideal.Quotient.mk_surjective (e.symm G)
    have h1 : Ideal.Quotient.mk (Ideal.span {V π}) z = Ideal.Quotient.mk (Ideal.span {V π}) (const π p * g') := by
      apply e.injective
      rw [hG, map_mul (Ideal.Quotient.mk _), map_mul e, heC, hg', RingEquiv.apply_symm_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h1
    obtain ⟨b, hb⟩ := h1
    have : z = const π p * g' + b * V π := by rw [hb]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

end Branch

section PS
variable {D : Type*} [CommRing D]

theorem isUnit_of_constantCoeff {f : PowerSeries D} (h : IsUnit (PowerSeries.constantCoeff f)) : IsUnit f :=
  PowerSeries.isUnit_iff_constantCoeff.mpr h

theorem X_mul_ne_zero [Nontrivial D] {u : PowerSeries D} (hu : IsUnit u) : PowerSeries.X * u ≠ 0 := by
  intro h
  obtain ⟨v, rfl⟩ := hu
  have : (PowerSeries.X : PowerSeries D) = 0 := by
    calc (PowerSeries.X : PowerSeries D) = PowerSeries.X * (v : PowerSeries D) * ((v⁻¹ : (PowerSeries D)ˣ) : PowerSeries D) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = 0 := by rw [h, zero_mul]
  exact PowerSeries.X_ne_zero this

end PS

section Abstract
variable {W : Type*} [CommRing W]

set_option maxHeartbeats 6400000 in

theorem pins_abstract (p : W) (N : ℕ) (hN : 0 < N) [IsDomain (W ⧸ Ideal.span {p})]
    [IsLocalRing (UVCrossingModel W (p ^ N))]
    (hmaxM : IsLocalRing.maximalIdeal (UVCrossingModel W (p ^ N)) = Ideal.span {UVCrossingModel.const (p ^ N) (p), UVCrossingModel.U (p ^ N), UVCrossingModel.V (p ^ N)})
    (q : ℕ) (hqP : q.Prime) (hqW : ((q : ℕ) : W) ∈ Ideal.span {p})
    (xW xqW : W) (hxq : xqW = xW ^ q) (hxW : xW - xqW ^ q ∈ Ideal.span {p})
    (c cq : (UVCrossingModel W (p ^ N))ˣ) (r rq : UVCrossingModel W (p ^ N))
    (hr : r ∈ Ideal.span {UVCrossingModel.const (p ^ N) (p)} ⊔ Ideal.span {UVCrossingModel.const (p ^ N) (p), UVCrossingModel.U (p ^ N), UVCrossingModel.V (p ^ N)} ^ 2)
    (hrq : rq ∈ Ideal.span {UVCrossingModel.const (p ^ N) (p)} ⊔ Ideal.span {UVCrossingModel.const (p ^ N) (p), UVCrossingModel.U (p ^ N), UVCrossingModel.V (p ^ N)} ^ 2)
    (m₀ : UVCrossingModel W (p ^ N))
    (hprodM : (((c : UVCrossingModel W (p ^ N)) * UVCrossingModel.V (p ^ N) + r + UVCrossingModel.const (p ^ N) (xW)) ^ q - ((cq : UVCrossingModel W (p ^ N)) * UVCrossingModel.U (p ^ N) + rq + UVCrossingModel.const (p ^ N) (xqW))) * (((c : UVCrossingModel W (p ^ N)) * UVCrossingModel.V (p ^ N) + r + UVCrossingModel.const (p ^ N) (xW)) - ((cq : UVCrossingModel W (p ^ N)) * UVCrossingModel.U (p ^ N) + rq + UVCrossingModel.const (p ^ N) (xqW)) ^ q) = m₀ * ((q : ℕ) : UVCrossingModel W (p ^ N))) :
    Ideal.span {UVCrossingModel.const (p ^ N) (p), ((cq : UVCrossingModel W (p ^ N)) * UVCrossingModel.U (p ^ N) + rq + UVCrossingModel.const (p ^ N) (xqW)) - ((c : UVCrossingModel W (p ^ N)) * UVCrossingModel.V (p ^ N) + r + UVCrossingModel.const (p ^ N) (xW)) ^ q} = Ideal.span {UVCrossingModel.const (p ^ N) (p), UVCrossingModel.U (p ^ N)} ∧
    Ideal.span {UVCrossingModel.const (p ^ N) (p), ((c : UVCrossingModel W (p ^ N)) * UVCrossingModel.V (p ^ N) + r + UVCrossingModel.const (p ^ N) (xW)) - ((cq : UVCrossingModel W (p ^ N)) * UVCrossingModel.U (p ^ N) + rq + UVCrossingModel.const (p ^ N) (xqW)) ^ q} = Ideal.span {UVCrossingModel.const (p ^ N) (p), UVCrossingModel.V (p ^ N)} := by
  classical
  have hle : Ideal.span {p ^ N} ≤ Ideal.span {p} := Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self _ hN.ne')
  obtain ⟨ρ₁, hρ₁U, hρ₁V, hρ₁C, hρ₁ker⟩ := exists_branchMapV (p ^ N) p hle
  obtain ⟨ρ₂, hρ₂V, hρ₂U, hρ₂C, hρ₂ker⟩ := exists_branchMapU (p ^ N) p hle
  have hmk0 : ∀ w : W, w ∈ Ideal.span {p} → (Ideal.Quotient.mk (Ideal.span {p}) w) = 0 :=
    fun w hw => Ideal.Quotient.eq_zero_iff_mem.mpr hw
  have hpspan : p ∈ Ideal.span {p} := Ideal.mem_span_singleton_self _
  have hρ₁π : ρ₁ (UVCrossingModel.const (p ^ N) (p)) = 0 := by rw [hρ₁C, hmk0 _ hpspan, map_zero]
  have hρ₂π : ρ₂ (UVCrossingModel.const (p ^ N) (p)) = 0 := by rw [hρ₂C, hmk0 _ hpspan, map_zero]
  have hqM : ((q : ℕ) : UVCrossingModel W (p ^ N)) = UVCrossingModel.const (p ^ N) ((q : ℕ) : W) := by
    rw [← map_natCast (UVCrossingModel.constHom (p ^ N)) q, UVCrossingModel.constHom_apply]
  have hρ₁q : ρ₁ ((q : ℕ) : UVCrossingModel W (p ^ N)) = 0 := by rw [hqM, hρ₁C, hmk0 _ hqW, map_zero]
  have hρ₂q : ρ₂ ((q : ℕ) : UVCrossingModel W (p ^ N)) = 0 := by rw [hqM, hρ₂C, hmk0 _ hqW, map_zero]
  have hρ₁q' : ((q : ℕ) : PowerSeries (W ⧸ Ideal.span {p})) = 0 := by rw [← map_natCast ρ₁ q, hρ₁q]
  have hρ₂q' : ((q : ℕ) : PowerSeries (W ⧸ Ideal.span {p})) = 0 := by rw [← map_natCast ρ₂ q, hρ₂q]
  have hρx : ∀ ρ : UVCrossingModel W (p ^ N) →+* PowerSeries (W ⧸ Ideal.span {p}), (∀ w, ρ (UVCrossingModel.const (p ^ N) w) = PowerSeries.C (Ideal.Quotient.mk (Ideal.span {p}) w)) →
      ρ (UVCrossingModel.const (p ^ N) (xW)) = ρ (UVCrossingModel.const (p ^ N) (xqW)) ^ q := by
    intro ρ hρC
    rw [hρC, hρC, ← map_pow, ← map_pow, ← sub_eq_zero, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hxW, map_zero]

  obtain ⟨r₁, hr₁⟩ : ∃ z₁ : PowerSeries (W ⧸ Ideal.span {p}), ρ₁ r = PowerSeries.X ^ 2 * z₁ := by
    have hgen1 : ∀ m ∈ Ideal.span {UVCrossingModel.const (p ^ N) (p), UVCrossingModel.U (p ^ N), UVCrossingModel.V (p ^ N)}, ρ₁ m ∈ Ideal.span {(PowerSeries.X : PowerSeries (W ⧸ Ideal.span {p}))} := by
      intro m hm
      induction hm using Submodule.span_induction with
      | mem u hu =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl | rfl
        · rw [hρ₁π]; exact zero_mem _
        · rw [hρ₁U]; exact zero_mem _
        · rw [hρ₁V]; exact Ideal.mem_span_singleton_self _
      | zero => rw [map_zero]; exact zero_mem _
      | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
      | smul b u _ hu => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hu
    obtain ⟨yy, hyy, zz, hzz, hsum⟩ := Submodule.mem_sup.mp hr
    obtain ⟨ay, hay⟩ := Ideal.mem_span_singleton'.mp hyy
    rw [pow_two] at hzz
    have hzzX : ρ₁ zz ∈ Ideal.span {(PowerSeries.X : PowerSeries (W ⧸ Ideal.span {p})) ^ 2} := by
      refine Submodule.mul_induction_on hzz (fun m hm n hn => ?_) (fun u v hu hv => ?_)
      · rw [map_mul ρ₁]
        obtain ⟨m₁, hm₁⟩ := Ideal.mem_span_singleton'.mp (hgen1 m hm)
        obtain ⟨n₁, hn₁⟩ := Ideal.mem_span_singleton'.mp (hgen1 n hn)
        rw [← hm₁, ← hn₁]
        exact Ideal.mem_span_singleton'.mpr ⟨m₁ * n₁, by ring⟩
      · rw [map_add ρ₁]; exact add_mem hu hv
    obtain ⟨z₁, hz₁⟩ := Ideal.mem_span_singleton'.mp hzzX
    exact ⟨z₁, by rw [← hsum, map_add ρ₁, ← hay, map_mul ρ₁, hρ₁π, mul_zero, zero_add, ← hz₁, mul_comm]⟩
  obtain ⟨r₂, hr₂⟩ : ∃ z₁ : PowerSeries (W ⧸ Ideal.span {p}), ρ₁ rq = PowerSeries.X ^ 2 * z₁ := by
    have hgen1 : ∀ m ∈ Ideal.span {UVCrossingModel.const (p ^ N) (p), UVCrossingModel.U (p ^ N), UVCrossingModel.V (p ^ N)}, ρ₁ m ∈ Ideal.span {(PowerSeries.X : PowerSeries (W ⧸ Ideal.span {p}))} := by
      intro m hm
      induction hm using Submodule.span_induction with
      | mem u hu =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl | rfl
        · rw [hρ₁π]; exact zero_mem _
        · rw [hρ₁U]; exact zero_mem _
        · rw [hρ₁V]; exact Ideal.mem_span_singleton_self _
      | zero => rw [map_zero]; exact zero_mem _
      | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
      | smul b u _ hu => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hu
    obtain ⟨yy, hyy, zz, hzz, hsum⟩ := Submodule.mem_sup.mp hrq
    obtain ⟨ay, hay⟩ := Ideal.mem_span_singleton'.mp hyy
    rw [pow_two] at hzz
    have hzzX : ρ₁ zz ∈ Ideal.span {(PowerSeries.X : PowerSeries (W ⧸ Ideal.span {p})) ^ 2} := by
      refine Submodule.mul_induction_on hzz (fun m hm n hn => ?_) (fun u v hu hv => ?_)
      · rw [map_mul ρ₁]
        obtain ⟨m₁, hm₁⟩ := Ideal.mem_span_singleton'.mp (hgen1 m hm)
        obtain ⟨n₁, hn₁⟩ := Ideal.mem_span_singleton'.mp (hgen1 n hn)
        rw [← hm₁, ← hn₁]
        exact Ideal.mem_span_singleton'.mpr ⟨m₁ * n₁, by ring⟩
      · rw [map_add ρ₁]; exact add_mem hu hv
    obtain ⟨z₁, hz₁⟩ := Ideal.mem_span_singleton'.mp hzzX
    exact ⟨z₁, by rw [← hsum, map_add ρ₁, ← hay, map_mul ρ₁, hρ₁π, mul_zero, zero_add, ← hz₁, mul_comm]⟩
  obtain ⟨r₃, hr₃⟩ : ∃ z₁ : PowerSeries (W ⧸ Ideal.span {p}), ρ₂ r = PowerSeries.X ^ 2 * z₁ := by
    have hgen1 : ∀ m ∈ Ideal.span {UVCrossingModel.const (p ^ N) (p), UVCrossingModel.U (p ^ N), UVCrossingModel.V (p ^ N)}, ρ₂ m ∈ Ideal.span {(PowerSeries.X : PowerSeries (W ⧸ Ideal.span {p}))} := by
      intro m hm
      induction hm using Submodule.span_induction with
      | mem u hu =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl | rfl
        · rw [hρ₂π]; exact zero_mem _
        · rw [hρ₂U]; exact Ideal.mem_span_singleton_self _
        · rw [hρ₂V]; exact zero_mem _
      | zero => rw [map_zero]; exact zero_mem _
      | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
      | smul b u _ hu => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hu
    obtain ⟨yy, hyy, zz, hzz, hsum⟩ := Submodule.mem_sup.mp hr
    obtain ⟨ay, hay⟩ := Ideal.mem_span_singleton'.mp hyy
    rw [pow_two] at hzz
    have hzzX : ρ₂ zz ∈ Ideal.span {(PowerSeries.X : PowerSeries (W ⧸ Ideal.span {p})) ^ 2} := by
      refine Submodule.mul_induction_on hzz (fun m hm n hn => ?_) (fun u v hu hv => ?_)
      · rw [map_mul ρ₂]
        obtain ⟨m₁, hm₁⟩ := Ideal.mem_span_singleton'.mp (hgen1 m hm)
        obtain ⟨n₁, hn₁⟩ := Ideal.mem_span_singleton'.mp (hgen1 n hn)
        rw [← hm₁, ← hn₁]
        exact Ideal.mem_span_singleton'.mpr ⟨m₁ * n₁, by ring⟩
      · rw [map_add ρ₂]; exact add_mem hu hv
    obtain ⟨z₁, hz₁⟩ := Ideal.mem_span_singleton'.mp hzzX
    exact ⟨z₁, by rw [← hsum, map_add ρ₂, ← hay, map_mul ρ₂, hρ₂π, mul_zero, zero_add, ← hz₁, mul_comm]⟩
  obtain ⟨r₄, hr₄⟩ : ∃ z₁ : PowerSeries (W ⧸ Ideal.span {p}), ρ₂ rq = PowerSeries.X ^ 2 * z₁ := by
    have hgen1 : ∀ m ∈ Ideal.span {UVCrossingModel.const (p ^ N) (p), UVCrossingModel.U (p ^ N), UVCrossingModel.V (p ^ N)}, ρ₂ m ∈ Ideal.span {(PowerSeries.X : PowerSeries (W ⧸ Ideal.span {p}))} := by
      intro m hm
      induction hm using Submodule.span_induction with
      | mem u hu =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl | rfl
        · rw [hρ₂π]; exact zero_mem _
        · rw [hρ₂U]; exact Ideal.mem_span_singleton_self _
        · rw [hρ₂V]; exact zero_mem _
      | zero => rw [map_zero]; exact zero_mem _
      | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
      | smul b u _ hu => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hu
    obtain ⟨yy, hyy, zz, hzz, hsum⟩ := Submodule.mem_sup.mp hrq
    obtain ⟨ay, hay⟩ := Ideal.mem_span_singleton'.mp hyy
    rw [pow_two] at hzz
    have hzzX : ρ₂ zz ∈ Ideal.span {(PowerSeries.X : PowerSeries (W ⧸ Ideal.span {p})) ^ 2} := by
      refine Submodule.mul_induction_on hzz (fun m hm n hn => ?_) (fun u v hu hv => ?_)
      · rw [map_mul ρ₂]
        obtain ⟨m₁, hm₁⟩ := Ideal.mem_span_singleton'.mp (hgen1 m hm)
        obtain ⟨n₁, hn₁⟩ := Ideal.mem_span_singleton'.mp (hgen1 n hn)
        rw [← hm₁, ← hn₁]
        exact Ideal.mem_span_singleton'.mpr ⟨m₁ * n₁, by ring⟩
      · rw [map_add ρ₂]; exact add_mem hu hv
    obtain ⟨z₁, hz₁⟩ := Ideal.mem_span_singleton'.mp hzzX
    exact ⟨z₁, by rw [← hsum, map_add ρ₂, ← hay, map_mul ρ₂, hρ₂π, mul_zero, zero_add, ← hz₁, mul_comm]⟩

  have hcu : IsUnit (ρ₁ (c : UVCrossingModel W (p ^ N))) := (Units.isUnit c).map ρ₁
  have hcqu : IsUnit (ρ₂ (cq : UVCrossingModel W (p ^ N))) := (Units.isUnit cq).map ρ₂
  have hX2q : (PowerSeries.X : PowerSeries (W ⧸ Ideal.span {p})) ^ 2 * PowerSeries.X ^ (2 * q - 2) = (PowerSeries.X ^ 2) ^ q := by
    rw [← pow_mul, ← pow_add]; congr 1; have := hqP.two_le; omega

  obtain ⟨w₁, hw₁⟩ := exists_add_pow_prime_eq hqP (PowerSeries.X ^ 2 * r₂ : PowerSeries (W ⧸ Ideal.span {p})) (ρ₁ (UVCrossingModel.const (p ^ N) (xqW)))
  have hρ₁t' : ρ₁ (((c : UVCrossingModel W (p ^ N)) * UVCrossingModel.V (p ^ N) + r + UVCrossingModel.const (p ^ N) (xW)) - ((cq : UVCrossingModel W (p ^ N)) * UVCrossingModel.U (p ^ N) + rq + UVCrossingModel.const (p ^ N) (xqW)) ^ q) =
      PowerSeries.X * (ρ₁ (c : UVCrossingModel W (p ^ N)) + PowerSeries.X * (r₁ - PowerSeries.X ^ (2 * q - 2) * r₂ ^ q)) := by
    rw [map_sub ρ₁, map_pow ρ₁, map_add ρ₁, map_add ρ₁, map_add ρ₁, map_add ρ₁, map_mul ρ₁, map_mul ρ₁, hρ₁V, hρ₁U, mul_zero,
      zero_add, hr₁, hr₂, hρx ρ₁ hρ₁C, hw₁, hρ₁q']
    rw [mul_pow, ← hX2q]
    ring
  have hu₁ : IsUnit (ρ₁ (c : UVCrossingModel W (p ^ N)) + PowerSeries.X * (r₁ - PowerSeries.X ^ (2 * q - 2) * r₂ ^ q)) := by
    apply isUnit_of_constantCoeff
    rw [map_add, map_mul, PowerSeries.constantCoeff_X, zero_mul, add_zero]
    exact hcu.map _

  obtain ⟨w₂, hw₂⟩ := exists_add_pow_prime_eq hqP (PowerSeries.X ^ 2 * r₃ : PowerSeries (W ⧸ Ideal.span {p})) (ρ₂ (UVCrossingModel.const (p ^ N) (xW)))
  have hρ₂t : ρ₂ (((cq : UVCrossingModel W (p ^ N)) * UVCrossingModel.U (p ^ N) + rq + UVCrossingModel.const (p ^ N) (xqW)) - ((c : UVCrossingModel W (p ^ N)) * UVCrossingModel.V (p ^ N) + r + UVCrossingModel.const (p ^ N) (xW)) ^ q) =
      PowerSeries.X * (ρ₂ (cq : UVCrossingModel W (p ^ N)) + PowerSeries.X * (r₄ - PowerSeries.X ^ (2 * q - 2) * r₃ ^ q)) := by
    have hxq' : ρ₂ (UVCrossingModel.const (p ^ N) (xqW)) = ρ₂ (UVCrossingModel.const (p ^ N) (xW)) ^ q := by
      rw [hρ₂C, hρ₂C, hxq, map_pow, map_pow]
    rw [map_sub ρ₂, map_pow ρ₂, map_add ρ₂, map_add ρ₂, map_add ρ₂, map_add ρ₂, map_mul ρ₂, map_mul ρ₂, hρ₂V, hρ₂U, mul_zero,
      zero_add, hr₃, hr₄, hxq', hw₂, hρ₂q']
    rw [mul_pow, ← hX2q]
    ring
  have hu₂ : IsUnit (ρ₂ (cq : UVCrossingModel W (p ^ N)) + PowerSeries.X * (r₄ - PowerSeries.X ^ (2 * q - 2) * r₃ ^ q)) := by
    apply isUnit_of_constantCoeff
    rw [map_add, map_mul, PowerSeries.constantCoeff_X, zero_mul, add_zero]
    exact hcqu.map _

  have ht_mem : ((cq : UVCrossingModel W (p ^ N)) * UVCrossingModel.U (p ^ N) + rq + UVCrossingModel.const (p ^ N) (xqW)) - ((c : UVCrossingModel W (p ^ N)) * UVCrossingModel.V (p ^ N) + r + UVCrossingModel.const (p ^ N) (xW)) ^ q ∈ Ideal.span {UVCrossingModel.const (p ^ N) (p), UVCrossingModel.U (p ^ N)} := by
    apply hρ₁ker
    have h := congrArg ρ₁ hprodM
    rw [map_mul ρ₁, hρ₁t', map_mul ρ₁, hρ₁q, mul_zero] at h
    have h' := (mul_eq_zero.mp h).resolve_right (X_mul_ne_zero hu₁)
    rw [← neg_sub, map_neg ρ₁, h', neg_zero]
  have ht'_mem : ((c : UVCrossingModel W (p ^ N)) * UVCrossingModel.V (p ^ N) + r + UVCrossingModel.const (p ^ N) (xW)) - ((cq : UVCrossingModel W (p ^ N)) * UVCrossingModel.U (p ^ N) + rq + UVCrossingModel.const (p ^ N) (xqW)) ^ q ∈ Ideal.span {UVCrossingModel.const (p ^ N) (p), UVCrossingModel.V (p ^ N)} := by
    apply hρ₂ker
    have h := congrArg ρ₂ hprodM
    rw [map_mul ρ₂, map_mul ρ₂, hρ₂q, mul_zero] at h
    have hne : ρ₂ (((c : UVCrossingModel W (p ^ N)) * UVCrossingModel.V (p ^ N) + r + UVCrossingModel.const (p ^ N) (xW)) ^ q - ((cq : UVCrossingModel W (p ^ N)) * UVCrossingModel.U (p ^ N) + rq + UVCrossingModel.const (p ^ N) (xqW))) ≠ 0 := by
      rw [← neg_sub, map_neg ρ₂, hρ₂t, neg_ne_zero]
      exact X_mul_ne_zero hu₂
    exact (mul_eq_zero.mp h).resolve_left hne

  have hunit : ∀ (ρ : UVCrossingModel W (p ^ N) →+* PowerSeries (W ⧸ Ideal.span {p})), ρ (UVCrossingModel.const (p ^ N) (p)) = 0 →
      (ρ (UVCrossingModel.U (p ^ N)) = 0 ∧ ρ (UVCrossingModel.V (p ^ N)) = PowerSeries.X ∨ ρ (UVCrossingModel.V (p ^ N)) = 0 ∧ ρ (UVCrossingModel.U (p ^ N)) = PowerSeries.X) →
      ∀ β : UVCrossingModel W (p ^ N), IsUnit (ρ β) → IsUnit β := by
    intro ρ hρπ hρUV
    have hXgen : ∀ m ∈ Ideal.span {UVCrossingModel.const (p ^ N) (p), UVCrossingModel.U (p ^ N), UVCrossingModel.V (p ^ N)}, ρ m ∈ Ideal.span {(PowerSeries.X : PowerSeries (W ⧸ Ideal.span {p}))} := by
      intro m hm
      induction hm using Submodule.span_induction with
      | mem u hu =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl | rfl
        · rw [hρπ]; exact zero_mem _
        · rcases hρUV with ⟨hU, -⟩ | ⟨-, hU⟩
          · rw [hU]; exact zero_mem _
          · rw [hU]; exact Ideal.mem_span_singleton_self _
        · rcases hρUV with ⟨-, hV⟩ | ⟨hV, -⟩
          · rw [hV]; exact Ideal.mem_span_singleton_self _
          · rw [hV]; exact zero_mem _
      | zero => rw [map_zero]; exact zero_mem _
      | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
      | smul b u _ hu => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hu
    intro β hβ
    by_contra hβu
    have hβm : β ∈ IsLocalRing.maximalIdeal (UVCrossingModel W (p ^ N)) := (IsLocalRing.mem_maximalIdeal _).mpr hβu
    rw [hmaxM] at hβm
    have hX := hXgen β hβm
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hX
    have := PowerSeries.isUnit_iff_constantCoeff.mp hβ
    rw [hX] at this
    exact not_isUnit_zero this

  have hU_mem : UVCrossingModel.U (p ^ N) ∈ Ideal.span {UVCrossingModel.const (p ^ N) (p), ((cq : UVCrossingModel W (p ^ N)) * UVCrossingModel.U (p ^ N) + rq + UVCrossingModel.const (p ^ N) (xqW)) - ((c : UVCrossingModel W (p ^ N)) * UVCrossingModel.V (p ^ N) + r + UVCrossingModel.const (p ^ N) (xW)) ^ q} := by
    set tU := ((cq : UVCrossingModel W (p ^ N)) * UVCrossingModel.U (p ^ N) + rq + UVCrossingModel.const (p ^ N) (xqW)) - ((c : UVCrossingModel W (p ^ N)) * UVCrossingModel.V (p ^ N) + r + UVCrossingModel.const (p ^ N) (xW)) ^ q with htU
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp ht_mem
    have h := congrArg ρ₂ hαβ
    rw [map_add ρ₂, map_mul ρ₂, map_mul ρ₂, hρ₂π, mul_zero, zero_add, hρ₂U, hρ₂t, mul_comm] at h
    have hβ : ρ₂ β = ρ₂ (cq : UVCrossingModel W (p ^ N)) + PowerSeries.X * (r₄ - PowerSeries.X ^ (2 * q - 2) * r₃ ^ q) := by
      have h' : PowerSeries.X * (ρ₂ β - (ρ₂ (cq : UVCrossingModel W (p ^ N)) + PowerSeries.X * (r₄ - PowerSeries.X ^ (2 * q - 2) * r₃ ^ q))) = 0 := by
        rw [mul_sub, h, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left PowerSeries.X_ne_zero)
    have hβu : IsUnit β := hunit ρ₂ hρ₂π (Or.inr ⟨hρ₂V, hρ₂U⟩) β (hβ ▸ hu₂)
    obtain ⟨βu, rfl⟩ := hβu
    have hU : UVCrossingModel.U (p ^ N) = ↑βu⁻¹ * tU + (-(↑βu⁻¹ * α)) * UVCrossingModel.const (p ^ N) (p) := by
      rw [← hαβ, mul_add, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]; ring
    rw [hU]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr rfl))))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
  have hV_mem : UVCrossingModel.V (p ^ N) ∈ Ideal.span {UVCrossingModel.const (p ^ N) (p), ((c : UVCrossingModel W (p ^ N)) * UVCrossingModel.V (p ^ N) + r + UVCrossingModel.const (p ^ N) (xW)) - ((cq : UVCrossingModel W (p ^ N)) * UVCrossingModel.U (p ^ N) + rq + UVCrossingModel.const (p ^ N) (xqW)) ^ q} := by
    set tV := ((c : UVCrossingModel W (p ^ N)) * UVCrossingModel.V (p ^ N) + r + UVCrossingModel.const (p ^ N) (xW)) - ((cq : UVCrossingModel W (p ^ N)) * UVCrossingModel.U (p ^ N) + rq + UVCrossingModel.const (p ^ N) (xqW)) ^ q with htV
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp ht'_mem
    have h := congrArg ρ₁ hαβ
    rw [map_add ρ₁, map_mul ρ₁, map_mul ρ₁, hρ₁π, mul_zero, zero_add, hρ₁V, hρ₁t', mul_comm] at h
    have hβ : ρ₁ β = ρ₁ (c : UVCrossingModel W (p ^ N)) + PowerSeries.X * (r₁ - PowerSeries.X ^ (2 * q - 2) * r₂ ^ q) := by
      have h' : PowerSeries.X * (ρ₁ β - (ρ₁ (c : UVCrossingModel W (p ^ N)) + PowerSeries.X * (r₁ - PowerSeries.X ^ (2 * q - 2) * r₂ ^ q))) = 0 := by
        rw [mul_sub, h, sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left PowerSeries.X_ne_zero)
    have hβu : IsUnit β := hunit ρ₁ hρ₁π (Or.inl ⟨hρ₁U, hρ₁V⟩) β (hβ ▸ hu₁)
    obtain ⟨βu, rfl⟩ := hβu
    have hV : UVCrossingModel.V (p ^ N) = ↑βu⁻¹ * tV + (-(↑βu⁻¹ * α)) * UVCrossingModel.const (p ^ N) (p) := by
      rw [← hαβ, mul_add, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]; ring
    rw [hV]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr rfl))))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))

  constructor
  · apply le_antisymm
    · rw [Ideal.span_le, Set.pair_subset_iff]
      exact ⟨Ideal.subset_span (Set.mem_insert _ _), ht_mem⟩
    · rw [Ideal.span_le, Set.pair_subset_iff]
      exact ⟨Ideal.subset_span (Set.mem_insert _ _), hU_mem⟩
  · apply le_antisymm
    · rw [Ideal.span_le, Set.pair_subset_iff]
      exact ⟨Ideal.subset_span (Set.mem_insert _ _), ht'_mem⟩
    · rw [Ideal.span_le, Set.pair_subset_iff]
      exact ⟨Ideal.subset_span (Set.mem_insert _ _), hV_mem⟩

end Abstract

end Ws30Pins
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC qExpand ssJSet jWidth jWidth_pos UVCrossingModel UVCrossingModel.U UVCrossingModel.V UVCrossingModel.const UVCrossingModel.constHom UVCrossingModel.constHom_apply UVCrossingModel.exists_ringEquiv_quotient_span_U_powerSeries UVCrossingModel.exists_ringEquiv_quotient_span_V_powerSeries UVCrossingModel.maximalIdeal_eq_map_maximalIdeal_sup_span_pair UVCrossingModel.isLocalRing_of_not_isUnit NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing"
p2m_open "ModularCurve"
namespace Ws30PinsMain

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

section RedLemmas
variable {A : ValuationSubring Qb} {k : Type*} [Field k]

theorem mem_coeffSubring_iff' (K : IntermediateField ℚ Qb) {x : Qb} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K := Iff.rfl

theorem red_eq_zero_of_mem_maximalIdeal (red : A →+* k) (q : ℕ) [Fact q.Prime] [CharP k q] (τ : A) (hτ : τ ∈ IsLocalRing.maximalIdeal A) : red τ = 0 := by
  have hq : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  have hA : A.LiesOverPrime q := by
    rw [ValuationSubring.LiesOverPrime, ValuationSubring.mem_nonunits_iff]
    have hnu : ¬ IsUnit (⟨(q : AlgebraicClosure ℚ), hq⟩ : A) := by
      intro hu
      have h1 := hu.map red
      have h0 : red ⟨(q : AlgebraicClosure ℚ), hq⟩ = 0 := by
        have : (⟨(q : AlgebraicClosure ℚ), hq⟩ : A) = (q : A) := Subtype.ext (by push_cast; rfl)
        rw [this, map_natCast, CharP.cast_eq_zero]
      rw [h0] at h1
      exact not_isUnit_zero h1
    exact (ValuationSubring.valuation_lt_one_iff A ⟨(q : AlgebraicClosure ℚ), hq⟩).mp
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
  exact ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP A q hA red τ
    ((ValuationSubring.valuation_lt_one_iff A τ).mp hτ)

theorem isUnit_coeffSubring_iff (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    (c : ↥(coeffSubring A K)) : IsUnit c ↔ redRestrict red K c ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ hc
    have h1 : redRestrict red K ((u * u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) = 1 := by
      rw [mul_inv_cancel, Units.val_one, map_one]
    rw [Units.val_mul, map_mul, hc, zero_mul] at h1
    exact zero_ne_one h1
  · intro hc
    have hcA : (c : Qb) ∈ A := ((mem_coeffSubring_iff' (A := A) K).mp c.2).1
    have hcK : (c : Qb) ∈ K := ((mem_coeffSubring_iff' (A := A) K).mp c.2).2
    have hcm : (⟨(c : Qb), hcA⟩ : A) ∉ IsLocalRing.maximalIdeal A := fun hm =>
      hc (red_eq_zero_of_mem_maximalIdeal red q _ hm)
    have hu : IsUnit (⟨(c : Qb), hcA⟩ : A) := by
      by_contra h; exact hcm ((IsLocalRing.mem_maximalIdeal _).mpr h)
    obtain ⟨u, hu⟩ := hu
    have hmul : (((u⁻¹ : Aˣ) : A) : Qb) * (c : Qb) = 1 := by
      have h := congrArg (fun z : A => (z : Qb)) u.inv_mul
      rw [hu] at h
      simpa using h
    have hinv : (c : Qb)⁻¹ = (((u⁻¹ : Aˣ) : A) : Qb) := inv_eq_of_mul_eq_one_left hmul
    have hinvmem : (c : Qb)⁻¹ ∈ coeffSubring A K :=
      (mem_coeffSubring_iff' (A := A) K).mpr ⟨hinv ▸ ((u⁻¹ : Aˣ) : A).2, K.inv_mem hcK⟩
    have hc0 : (c : Qb) ≠ 0 := by
      rintro h0
      apply hc
      have : c = 0 := Subtype.ext h0
      rw [this, map_zero]
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvmem⟩, Subtype.ext (mul_inv_cancel₀ hc0)⟩

theorem stepA_dvr (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    [FiniteDimensional ℚ K] : IsDiscreteValuationRing ↥(coeffSubring A K) := by
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with h | h
  · exfalso
    have hqK : ((q : ℕ) : Qb)⁻¹ ∈ coeffSubring A K := by
      rw [h]; exact (K.inv_mem (natCast_mem K q) : ((q : ℕ) : Qb)⁻¹ ∈ K)
    have hu : IsUnit (((q : ℕ) : ↥(coeffSubring A K))) :=
      isUnit_iff_exists_inv.mpr ⟨⟨_, hqK⟩, Subtype.ext (by
        push_cast
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))⟩
    have := (isUnit_coeffSubring_iff red K q _).mp hu
    apply this
    rw [map_natCast, CharP.cast_eq_zero]
  · exact h

theorem stepA_uniformizer (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    [FiniteDimensional ℚ K] :
    ∃ ϖ : ↥(coeffSubring A K), Irreducible ϖ ∧ (∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d) ∧
      ∃ (e : ℕ) (ε : ↥(coeffSubring A K)), 1 ≤ e ∧ IsUnit ε ∧ ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ e * ε := by
  classical
  haveI := stepA_dvr red K q
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K)
  have hker : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d := by
    intro c
    have h1 : redRestrict red K c = 0 ↔ ¬ IsUnit c := by
      rw [isUnit_coeffSubring_iff red K q c, not_not]
    rw [h1, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
    exact Iff.rfl
  refine ⟨ϖ, hϖ, hker, ?_⟩
  have hq0 : ((q : ℕ) : ↥(coeffSubring A K)) ≠ 0 := by
    intro h
    have := congrArg (fun z : ↥(coeffSubring A K) => (z : Qb)) h
    push_cast at this
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hϖ
  refine ⟨n, u, ?_, u.isUnit, by rw [hn, mul_comm]⟩
  by_contra hlt
  have hn0 : n = 0 := by omega
  rw [hn0, pow_zero, mul_one] at hn
  have hu : IsUnit ((q : ℕ) : ↥(coeffSubring A K)) := hn ▸ u.isUnit
  exact ((isUnit_coeffSubring_iff red K q _).mp hu) (by rw [map_natCast, CharP.cast_eq_zero])

end RedLemmas

section Adic
variable {R : Type*} [CommRing R] (I : Ideal R)

theorem not_isUnit_of_of_mem (hI : I ≠ ⊤) {s : R} (hs : s ∈ I) : ¬ IsUnit (AdicCompletion.of I R s) := by
  intro hu
  have h1 := hu.map (AdicCompletion.evalₐ I 1)
  rw [AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem.mpr (by rwa [pow_one]), isUnit_zero_iff,
    Ideal.Quotient.zero_eq_one_iff, pow_one] at h1
  exact hI h1

theorem evalₐ_iterate_of_levelwise (g : R → R) (ĝ : AdicCompletion I R → AdicCompletion I R)
    (hĝ : ∀ (n : ℕ) (x : AdicCompletion I R) (z : R), Ideal.Quotient.mk (I ^ n) z = AdicCompletion.evalₐ I n x →
      AdicCompletion.evalₐ I n (ĝ x) = Ideal.Quotient.mk (I ^ n) (g z))
    (m n : ℕ) (x : AdicCompletion I R) (z : R) (hz : Ideal.Quotient.mk (I ^ n) z = AdicCompletion.evalₐ I n x) :
    AdicCompletion.evalₐ I n (ĝ^[m] x) = Ideal.Quotient.mk (I ^ n) (g^[m] z) := by
  induction m with
  | zero => simpa using hz.symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hĝ n _ _ ih.symm

theorem of_eq_of_levelwise (g : R → R) (ĝ : AdicCompletion I R → AdicCompletion I R)
    (hĝ : ∀ (n : ℕ) (x : AdicCompletion I R) (z : R), Ideal.Quotient.mk (I ^ n) z = AdicCompletion.evalₐ I n x →
      AdicCompletion.evalₐ I n (ĝ x) = Ideal.Quotient.mk (I ^ n) (g z)) (s : R) :
    ĝ (AdicCompletion.of I R s) = AdicCompletion.of I R (g s) :=
  AdicCompletion.ext_evalₐ fun n => by
    rw [hĝ n _ s (AdicCompletion.evalₐ_of I n s).symm, AdicCompletion.evalₐ_of]

theorem iterate_eq_self_of_levelwise (g : R → R) (ĝ : AdicCompletion I R → AdicCompletion I R)
    (hĝ : ∀ (n : ℕ) (x : AdicCompletion I R) (z : R), Ideal.Quotient.mk (I ^ n) z = AdicCompletion.evalₐ I n x →
      AdicCompletion.evalₐ I n (ĝ x) = Ideal.Quotient.mk (I ^ n) (g z))
    (e : ℕ) (hge : ∀ z, g^[e] z = z) (x : AdicCompletion I R) : ĝ^[e] x = x :=
  AdicCompletion.ext_evalₐ fun n => by
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    rw [evalₐ_iterate_of_levelwise I g ĝ hĝ e n x z hz, hge, hz]

end Adic

section W
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)

theorem isPrecomplete_map_mk {A : Type*} [CommRing A] (I J : Ideal A) [hI : IsPrecomplete I A] :
    IsPrecomplete (I.map (Ideal.Quotient.mk J)) (A ⧸ J) := by
  constructor
  intro f hf

  have hstep : ∀ n, f (n + 1) - f n ∈ (I ^ n).map (Ideal.Quotient.mk J) := by
    intro n
    have h := (hf (Nat.le_succ n)).symm
    rw [SModEq.sub_mem, ← Ideal.map_pow, smul_eq_mul, Ideal.mul_top] at h
    exact h

  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  choose d hd hdq using fun n => (Ideal.mem_map_iff_of_surjective _ hsurj).mp (hstep n)
  obtain ⟨g0, hg0⟩ := hsurj (f 0)
  let g : ℕ → A := fun n => Nat.rec g0 (fun k acc => acc + d k) n
  have hg_succ : ∀ n, g (n + 1) = g n + d n := fun n => rfl
  have hgf : ∀ n, Ideal.Quotient.mk J (g n) = f n := by
    intro n
    induction n with
    | zero => exact hg0
    | succ n ih => rw [hg_succ, map_add, ih, hdq]; ring

  have hgc : ∀ {m n : ℕ}, m ≤ n → g m ≡ g n [SMOD (I ^ m • ⊤ : Submodule A A)] := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
      refine ih.trans ?_
      rw [SModEq.sub_mem, hg_succ, smul_eq_mul, Ideal.mul_top]
      have : g n - (g n + d n) = -d n := by ring
      rw [this]
      exact Submodule.neg_mem _ (Ideal.pow_le_pow_right hmn (hd n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hI hgc
  refine ⟨Ideal.Quotient.mk J L, fun n => ?_⟩
  have h := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h
  rw [SModEq.sub_mem, ← hgf, ← map_sub, ← Ideal.map_pow, smul_eq_mul, Ideal.mul_top]
  exact Ideal.mem_map_of_mem _ h

abbrev IW : Ideal (PowerSeries O) := Ideal.span {(PowerSeries.X : PowerSeries O) - PowerSeries.C ϖ}

theorem W_facts (hϖ : Irreducible ϖ) : (IW ϖ).IsPrime ∧ IsPrincipalIdealRing (PowerSeries O ⧸ IW ϖ) ∧ IsLocalRing (PowerSeries O ⧸ IW ϖ)
    ∧ Irreducible (Ideal.Quotient.mk (IW ϖ) (PowerSeries.C ϖ)) := by
  have h := PowerSeries.quotient_span_X_sub_C_pow_of_irreducible ϖ hϖ 1 le_rfl
  rw [pow_one] at h
  exact h

end W
end Ws30PinsMain
end ModularCurve

end

open IsLocalRing _root_.ModularCurve _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_span_pair_eq_of_uvCrossingModel_apply_eq_qExpand_two_jq_sub_of_kroneckerCongruence.ModularCurve ModularCurve.UVCrossingModel ModularCurve.Ws30PinsMain in
set_option maxHeartbeats 12800000 in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (h01728 : a = 0 ∨ a = 1728)
    (l : k) (hl2 : l ^ (q ^ 2) = l) (hl0 : l ≠ 0) (hl1 : 16 * l ≠ 1)
    (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (eK : ℕ) (ε : ↥(coeffSubring A K)) (heK : 1 ≤ eK) (hε : IsUnit ε)
    (hqϖ : ((q : ℕ) : ↥(coeffSubring A K)) = ϖ ^ eK * ε)
    [IsNoetherianRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))]
    [IsLocalRing ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))]

    (g : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≃+* ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
    (hgC : ∀ o : ↥(coeffSubring A K), g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C o),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) = (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C o),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))))
    (hge : ∀ z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)), g^[jWidth a] z = z)

    (ζ₀ ζ₀' : ↥(coeffSubring A K))
    (hζe : redRestrict red K ζ₀ ^ jWidth a = 1)
    (hζprim : ∀ m : ℕ, 0 < m → m < jWidth a → redRestrict red K ζ₀ ^ m ≠ 1)
    (hζinv : redRestrict red K ζ₀ * redRestrict red K ζ₀' = 1)

    (htanH : g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
          - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ζ₀),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∈ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))), (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ^ 2
          ⊔ Ideal.span {((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))})
    (htanG : g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
          - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ζ₀'),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∈ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))), (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ^ 2
          ⊔ Ideal.span {((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))})

    (ĝ : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≃+* AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
    (hĝ : ∀ (n : ℕ) (x : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ^ n) z = AdicCompletion.evalₐ (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) n x →
        AdicCompletion.evalₐ (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) n (ĝ x) = Ideal.Quotient.mk (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ^ n) (g z))

    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (J Jq : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
    (hJ : (J : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) 2 (jqModC (AlgebraicClosure ℚ)))
    (hJq : (Jq : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) 2 (jqNModC (AlgebraicClosure ℚ) (1 * q)))

    (hgJ : g J = J) (hgJq : g Jq = Jq)

    (Φ : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) →+* AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
    (w w' : (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))ˣ)
    (hΦinj : Function.Injective Φ)
    (hΦfix : ∀ z : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)), z ∈ Set.range Φ ↔ ĝ z = z)
    (hΦC : ∀ o : ↥(coeffSubring A K), Φ (UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) (Ideal.Quotient.mk _ (PowerSeries.C o)))
          = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) _ (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C o),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))))
    (hΦU : Φ (UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) = (w : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) ^ jWidth a)
    (hΦV : Φ (UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) = (w' : AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))) ^ jWidth a)

    (c cq : (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)))ˣ) (r rq : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)))
    (hr : r ∈ Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ))} ⊔
        Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)), UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)), UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))} ^ 2)
    (hrq : rq ∈ Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ))} ⊔
        Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)), UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)), UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))} ^ 2)
    (hcr : Φ ((c : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) * UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) + r) =
        algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (J - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C x),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))))
    (hcq : Φ ((cq : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) * UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) + rq) =
        algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (Jq - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C (x ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))))

    (hKron : (J ^ q - Jq) * (J - Jq ^ q) ∈ Ideal.span {((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))}) :
    ∃ t t' : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)),
      Φ t = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (Jq - J ^ q) ∧
      Φ t' = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (J - Jq ^ q) ∧
      Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)), t} =
        Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)), UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))} ∧
      Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)), t'} =
        Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)), UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))} := by
  classical
  have hq2 : q ≠ 2 := by omega
  have hqP : q.Prime := Fact.out
  haveI hdvr : IsDiscreteValuationRing ↥(coeffSubring A K) := stepA_dvr red K q
  have hϖirr : Irreducible ϖ := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    ext c'
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_span_singleton,
      isUnit_coeffSubring_iff red K q c', not_not, hϖ c']
    constructor
    · rintro ⟨d, rfl⟩; exact ⟨d, rfl⟩
    · rintro ⟨d, rfl⟩; exact Dvd.intro d rfl
  obtain ⟨hprime, hpir, hlocW, hϖW⟩ := W_facts ϖ hϖirr
  haveI := hprime
  haveI : IsDomain (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) := Ideal.Quotient.isDomain _
  haveI := hpir
  haveI := hlocW
  haveI : IsDiscreteValuationRing (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) :=
    ⟨fun h0 => hϖW.ne_zero (by
      have hmem : ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ∈ maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) := hϖW.not_isUnit
      rw [h0] at hmem
      exact hmem)⟩
  have hmaxW : maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) = Ideal.span {((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ))} := hϖW.maximalIdeal_eq
  have hNpos : 0 < jWidth a * eK := Nat.mul_pos (jWidth_pos a) heK
  have hπm : ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK) ∈ maximalIdeal (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) := Ideal.pow_mem_of_mem _ hϖW.not_isUnit _ hNpos
  have hπu : ¬ IsUnit (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) := (mem_maximalIdeal _).mp hπm
  haveI hMloc : IsLocalRing (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) := ModularCurve.UVCrossingModel.isLocalRing_of_not_isUnit hπu
  have hmaxM : maximalIdeal (UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) = Ideal.span {UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ))), UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)), UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))} := by
    rw [ModularCurve.UVCrossingModel.maximalIdeal_eq_map_maximalIdeal_sup_span_pair hπu, hmaxW, Ideal.map_span,
      Set.image_singleton, UVCrossingModel.constHom_apply, ← Ideal.span_union, Set.singleton_union]
  haveI hpπ : (Ideal.span {((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ))}).IsPrime := by
    rw [← hmaxW]; exact (maximalIdeal.isMaximal _).isPrime
  haveI : IsDomain ((PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) ⧸ Ideal.span {((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ))}) := Ideal.Quotient.isDomain _
  have hπspan : ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ∈ Ideal.span {((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ))} := Ideal.mem_span_singleton_self _
  have hqW : ((q : ℕ) : (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) ∈ Ideal.span {((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ))} := by
    rw [← map_natCast ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})).comp PowerSeries.C) q,
      hqϖ, RingHom.comp_apply, map_mul, map_mul, map_pow, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hπspan _ heK)
  have ha2 : a ^ (q ^ 2) = a := by
    rcases h01728 with rfl | rfl
    · exact zero_pow (pow_ne_zero _ hqP.ne_zero)
    · have h1 : (((1728 : ℕ) : k)) ^ q = ((1728 : ℕ) : k) := by
        rw [← frobenius_def]; exact map_natCast (frobenius k q) 1728
      rw [show (1728 : k) = ((1728 : ℕ) : k) by norm_cast, pow_two, pow_mul, h1, h1]
  have hxq : (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x ^ q))) = (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x))) ^ q := by rw [map_pow, map_pow]
  have hxW : (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x))) - (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x ^ q))) ^ q ∈ Ideal.span {((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ))} := by
    have h0 : redRestrict red K (x - (x ^ q) ^ q) = 0 := by
      rw [map_sub, map_pow, map_pow, hx, ← pow_mul, ← pow_two, ha2, sub_self]
    obtain ⟨d, hd⟩ := (hϖ _).mp h0
    show ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})).comp PowerSeries.C) x -
        ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})).comp PowerSeries.C) (x ^ q) ^ q ∈ _
    rw [← map_pow, ← map_sub, hd, map_mul]
    exact Ideal.mul_mem_right _ _ hπspan

  have hΦPJ : Φ ((c : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) * UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) + r + UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x))))) = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) J := by
    rw [map_add Φ, hcr, hΦC, map_sub (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))), sub_add_cancel]
  have hΦPJq : Φ ((cq : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) * UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) + rq + UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x ^ q))))) = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) Jq := by
    rw [map_add Φ, hcq, hΦC, map_sub (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))), sub_add_cancel]
  obtain ⟨s₀, hs₀⟩ := Ideal.mem_span_singleton'.mp hKron
  have hgs₀ : g s₀ = s₀ := by
    have hfix : g ((J ^ q - Jq) * (J - Jq ^ q)) = (J ^ q - Jq) * (J - Jq ^ q) := by
      rw [map_mul g, map_sub g, map_sub g, map_pow g, map_pow g, hgJ, hgJq]
    rw [← hs₀, map_mul g, map_natCast g] at hfix
    haveI : CharZero (LaurentSeries (AlgebraicClosure ℚ)) :=
      charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) _).injective
    have hq0 : ((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ≠ 0 := by
      intro h
      have := congrArg (fun z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) => (z : LaurentSeries (AlgebraicClosure ℚ))) h
      simp only [Subring.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at this
      exact hqP.ne_zero this
    exact mul_right_cancel₀ hq0 hfix
  have hĝs₀ : ĝ (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) s₀) = algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) s₀ := by
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    conv_rhs => rw [← hgs₀]
    exact of_eq_of_levelwise _ g ĝ hĝ s₀
  obtain ⟨m₀, hm₀⟩ := (hΦfix _).mpr hĝs₀
  have hprodM : (((c : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) * UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) + r + UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x))))) ^ q - ((cq : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) * UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) + rq + UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x ^ q)))))) * (((c : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) * UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) + r + UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x))))) - ((cq : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) * UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) + rq + UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x ^ q))))) ^ q) = m₀ * ((q : ℕ) : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) := by
    apply hΦinj
    rw [map_mul Φ, map_sub Φ, map_sub Φ, map_pow Φ, map_pow Φ, hΦPJ, hΦPJq, map_mul Φ, hm₀, map_natCast Φ,
      ← map_pow (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))), ← map_pow (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))),
      ← map_sub (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))), ← map_sub (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))),
      ← map_mul (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))), ← hs₀, map_mul (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))),
      map_natCast (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))))]

  obtain ⟨h1, h2⟩ := Ws30Pins.pins_abstract ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) (jWidth a * eK) hNpos hmaxM q hqP hqW (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x))) (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x ^ q))) hxq hxW
    c cq r rq hr hrq m₀ hprodM
  refine ⟨((cq : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) * UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) + rq + UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x ^ q))))) - ((c : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) * UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) + r + UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x))))) ^ q, ((c : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) * UVCrossingModel.V (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) + r + UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x))))) - ((cq : UVCrossingModel (PowerSeries ↥(coeffSubring A K) ⧸ Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK))) * UVCrossingModel.U (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) + rq + UVCrossingModel.const (((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ})) (PowerSeries.C ϖ)) ^ (jWidth a * eK)) ((Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries ↥(coeffSubring A K)) - PowerSeries.C ϖ}) (PowerSeries.C (x ^ q))))) ^ q, ?_, ?_, h1, h2⟩
  · rw [map_sub Φ, map_pow Φ, hΦPJ, hΦPJq, ← map_pow (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))), ← map_sub (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))))]
  · rw [map_sub Φ, map_pow Φ, hΦPJ, hΦPJq, ← map_pow (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))), ← map_sub (algebraMap ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) (AdicCompletion (IsLocalRing.maximalIdeal ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))))]

end S_ModularCurve_LambdaNodeLocalized_exists_span_pair_eq_of_uvCrossingModel_apply_eq_qExpand_two_jq_sub_of_kroneckerCongruence
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_exists_span_pair_eq_of_uvCrossingModel_apply_eq_qExpand_two_jq_sub_of_kroneckerCongruence (solution)
