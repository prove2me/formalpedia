-- Prove2me | solution 1 for GlobalTheory.SW.TwistAdm.twist_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:07.989681+00:00
-- url     : https://prove2.me/submissions/5a351997-a350-4cbc-a863-e54f277d1ab5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Theorems.Thm_GlobalTheory_SW_TwistAdm_nat_smul_mem
import Theorems.Thm_GlobalTheory_SW_TwistAdm_cols_of_cond
import Theorems.Thm_GlobalTheory_SW_TwistAdm_exists_mult
import Theorems.Thm_GlobalTheory_SW_TwistAdm_twist_eq
import Theorems.Thm_GlobalTheory_SW_Base_nat_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable [IsCMField E]
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable [IsCMField E] in
private theorem adm_apply_add_mul_intCast_smul {M R : ℕ} {φ : _root_.GlobalTheory.SW.Fam E n N}
    (hφ : _root_.GlobalTheory.SW.admitted M R φ) {Λ : _root_.GlobalTheory.SW.Lt E n}
    (hΛ : Λ ∈ _root_.GlobalTheory.SW.Vset E n M) (x y : Matrix (Fin n) (Fin N) E)
    (hy : _root_.GlobalTheory.SW.ColsIn Λ y) (k : ℤ) : φ Λ (x + ((R : E) * (k : E)) • y) = φ Λ x := by
  have hnat : ∀ (z : Matrix (Fin n) (Fin N) E) (m : ℕ),
      φ Λ (z + ((R : E) * (m : E)) • y) = φ Λ z := by
    intro z m
    rw [mul_smul]
    refine hφ.per Λ hΛ z _ (fun a => ?_)
    rw [Matrix.transpose_smul]
    exact _root_.GlobalTheory.SW.TwistAdm.nat_smul_mem Λ m (hy a)
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa using hnat x m
  · have := hnat (x + ((R : E) * (((-(m : ℤ)) : ℤ) : E)) • y) m
    rw [← this]
    congr 1
    push_cast
    rw [add_assoc, ← add_smul]
    simp
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable [IsCMField E] in
private theorem adm_apply_mul_congr_one_mod_sq {M R : ℕ} {φ : _root_.GlobalTheory.SW.Fam E n N}
    (hφ : _root_.GlobalTheory.SW.admitted M R φ) {Λ : _root_.GlobalTheory.SW.Lt E n}
    (hΛ : Λ ∈ _root_.GlobalTheory.SW.Vset E n M) (x : Matrix (Fin n) (Fin N) E) {t u : ℕ}
    (hu : u ≡ 1 [MOD R ^ 2]) (ht : _root_.GlobalTheory.SW.ColsIn Λ ((R : E) • ((t : E) • x))) :
    φ Λ (((t * u : ℕ) : E) • x) = φ Λ ((t : E) • x) := by
  obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp hu.symm
  have hkE : (u : E) = 1 + (R : E) ^ 2 * (k : E) := by
    have := congrArg (Int.cast : ℤ → E) hk
    push_cast at this
    linear_combination this
  have e : ((t * u : ℕ) : E) = (t : E) + ((R : E) * (k : E)) * ((R : E) * (t : E)) := by
    push_cast
    rw [hkE]
    ring
  rw [← adm_apply_add_mul_intCast_smul hφ hΛ ((t : E) • x) _ ht k]
  congr 1
  simp only [e, add_smul, mul_smul]
end GlobalTheory.SW.TwistAdm
end

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable [IsCMField E]
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
variable [IsCMField E]
namespace GlobalTheory.SW.TwistAdm
namespace _root_.GlobalTheory.SW.TwistAdm
theorem _root_.solution {M R : ℕ} {φ : _root_.GlobalTheory.SW.Fam E n N}
    {𝔛 : _root_.GlobalTheory.SW.Lt E N} (hφ : _root_.GlobalTheory.SW.admitted M R φ)
    (hA : _root_.GlobalTheory.SW.Agree (R * M) 𝔛 (_root_.GlobalTheory.SW.stdL E N))
    {Λ : _root_.GlobalTheory.SW.Lt E n} (hΛ : Λ ∈ _root_.GlobalTheory.SW.Vset E n M)
    (x : Matrix (Fin n) (Fin N) E) (s : ℕ) (hs : s ≡ 1 [MOD R ^ 2])
    (h : ∀ ξ ∈ 𝔛, (R : E) • (x *ᵥ ξ) ∈ Λ) (hx : _root_.GlobalTheory.SW.ColsIn Λ ((R : E) • ((s : E) • x))) :
    _root_.GlobalTheory.SW.twist R 𝔛 φ Λ x = φ Λ ((s : E) • x) := by
  obtain ⟨-, hR⟩ := hφ.pos
  have hex := _root_.GlobalTheory.SW.TwistAdm.exists_mult hR hA
  rw [_root_.GlobalTheory.SW.TwistAdm.twist_eq φ hex, if_pos h]
  have hc0 := _root_.GlobalTheory.SW.TwistAdm.cols_of_cond hex.choose_spec.2 h
  rw [← adm_apply_mul_congr_one_mod_sq hφ hΛ x hs hc0, Nat.mul_comm hex.choose s,
    adm_apply_mul_congr_one_mod_sq hφ hΛ x hex.choose_spec.1 hx]
end _root_.GlobalTheory.SW.TwistAdm
end GlobalTheory.SW.TwistAdm
