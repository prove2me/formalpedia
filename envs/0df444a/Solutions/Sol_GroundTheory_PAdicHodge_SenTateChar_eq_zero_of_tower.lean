-- Prove2me | solution 1 for GroundTheory.PAdicHodge.SenTateChar.eq_zero_of_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:46.312745+00:00
-- url     : https://prove2.me/submissions/354908d8-bfbc-490b-99af-c5f5c4b5d5de

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharUnits
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_TateCpTwist
import Definitions.Def_GroundTheory_PAdicHodge_SenTateCharClosure
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_coe
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_mem
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_mul
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_smul
import Theorems.Thm_GroundTheory_PAdicHodge_extendToClosure_sub
import Theorems.Thm_GroundTheory_PAdicHodge_fixedPoints_closedSubgroup_eq_closure
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_add
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_map_of_map_eq
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_mul_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_zero
import Theorems.Thm_GroundTheory_PAdicHodge_norm_extendToClosure_le
import Theorems.Thm_GroundTheory_PAdicHodge_smul_mem_closureInCp
import Theorems.Thm_GroundTheory_PAdicHodge_sub_mem_closureInCp
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.normTrace_zero
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTraceF__apply_b99e2e848285
attribute [local simp] P2M_GroundTheory_PAdicHodge_normTrace__apply_81a03c79b867



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField
variable {p : ℕ} [hp : Fact p.Prime]
open GroundTheory.PAdicHodge.SenTateChar
open SenTateChar
namespace GroundTheory.PAdicHodge.SenTateChar
theorem _root_.solution (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (η : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ)
    (M : ℕ → IntermediateField K (PadicAlgCl p)) (hM : Monotone M)
    [∀ k, FiniteDimensional K (M k)]
    (hstab : ∀ (σ : Gal(PadicAlgCl p/K)) (k : ℕ), ∀ y ∈ M k, σ y ∈ M k)
    (hker : ∀ σ : Gal(PadicAlgCl p/K), (∀ k, σ ∈ (M k).fixingSubgroup) → η σ = 1)
    (C : ℝ) (n₁ : ℕ)
    (hbound : ∀ n, n₁ ≤ n → ∀ m, ∀ y ∈ M m, ‖normTrace (M n) y‖ ≤ C * ‖y‖)
    (hgen : ∀ n, n₁ ≤ n → ∃ γ ∈ (M n).fixingSubgroup, η γ ≠ 1)
    {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), algebraMap ℚ_[p] ℂ_[p] ((η σ : ℤ_[p]) : ℚ_[p]) * (σ • x) = x) :
    x = 0 := by
  classical
  set Ms : IntermediateField K (PadicAlgCl p) := ⨆ k, M k with hMs
  set E : IntermediateField ℚ_[p] (PadicAlgCl p) := Ms.restrictScalars ℚ_[p] with hE
  have hdir : Directed (· ≤ ·) M := hM.directed_le
  have hmemE : ∀ {y : PadicAlgCl p}, y ∈ E → ∃ m, y ∈ M m := fun {y} hy => by
    have h : y ∈ ((⨆ k, M k : IntermediateField K (PadicAlgCl p)) : Set (PadicAlgCl p)) :=
      (mem_restrictScalars _).1 hy
    rw [coe_iSup_of_directed hdir, Set.mem_iUnion] at h
    exact h
  have hME : ∀ {m} {y : PadicAlgCl p}, y ∈ M m → y ∈ E := fun {m} {y} hy =>
    (mem_restrictScalars _).2 (le_iSup M m hy)

  have hxc : x ∈ closureInCp E := by
    have hfixed : ∀ σ ∈ Ms.fixingSubgroup, σ • x = x := by
      intro σ hσ
      have h1 : η σ = 1 := hker σ fun k => by
        rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
        exact fun y hy => hσ y (le_iSup M k hy)
      have := hx σ
      rwa [h1, Units.val_one, PadicInt.coe_one, map_one, one_mul] at this
    have h := fixedPoints_closedSubgroup_eq_closure Ms.fixingSubgroup
      (InfiniteGalois.fixingSubgroup_isClosed Ms)
    have hx' : x ∈ {x : ℂ_[p] | ∀ σ ∈ Ms.fixingSubgroup, σ • x = x} := hfixed
    rw [h, InfiniteGalois.fixedField_fixingSubgroup] at hx'
    exact hx'

  have hC1 : 1 ≤ C := by
    have h := hbound n₁ le_rfl n₁ 1 (one_mem _)
    rwa [normTrace_of_mem _ (one_mem _), norm_one, mul_one] at h
  have hC0 : 0 ≤ C := zero_le_one.trans hC1

  have hadd : ∀ n, ∀ y ∈ E, ∀ z ∈ E, normTrace (M n) (y + z) = normTrace (M n) y + normTrace (M n) z :=
    fun n y _ z _ => normTrace_add _ y z
  have hbd : ∀ n, n₁ ≤ n → ∀ y ∈ E, ‖normTrace (M n) y‖ ≤ C * ‖y‖ := by
    intro n hn y hy
    obtain ⟨m, hm⟩ := hmemE hy
    exact hbound n hn m y hm
  have hmapsE : ∀ (σ : Gal(PadicAlgCl p/K)), ∀ y ∈ E, σ y ∈ E := by
    intro σ y hy
    obtain ⟨m, hm⟩ := hmemE hy
    exact hME (hstab σ m y hm)
  have hcomm : ∀ (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (y : PadicAlgCl p),
      normTrace (M n) (σ y) = σ (normTrace (M n) y) := by
    intro σ n y
    refine normTrace_map_of_map_eq (M n) σ ?_ y
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hstab σ n z hz
    · intro z hz
      refine ⟨σ⁻¹ z, hstab σ⁻¹ n z hz, ?_⟩
      change σ (σ⁻¹ z) = z
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

  have hR : ∀ n, n₁ ≤ n → extendToClosure E (normTrace (M n)) x = 0 := by
    intro n hn
    set k' : IntermediateField ℚ_[p] (PadicAlgCl p) := (M n).restrictScalars ℚ_[p]
    have : FiniteDimensional ℚ_[p] (M n) := Module.Finite.trans K (M n)
    have : FiniteDimensional ℚ_[p] k' := (inferInstance : FiniteDimensional ℚ_[p] (M n))
    have hkE : k' ≤ E := fun y hy => hME ((mem_restrictScalars _).1 hy)
    have hmaps : ∀ y ∈ E, normTrace (M n) y ∈ k' := fun y _ =>
      (mem_restrictScalars _).2 (normTrace_mem _ y)
    have hfix : ∀ a ∈ k', normTrace (M n) a = a := fun a ha =>
      normTrace_of_mem _ ((mem_restrictScalars _).1 ha)
    have hmul : ∀ a ∈ k', ∀ y ∈ E, normTrace (M n) (a * y) = a * normTrace (M n) y :=
      fun a ha y _ => normTrace_mul_of_mem _ ((mem_restrictScalars _).1 ha) y
    obtain ⟨γ, hγ, hγη⟩ := hgen n hn
    obtain ⟨b, hb, hbx⟩ := extendToClosure_mem (hadd n) (hbd n hn) hmaps hxc

    set q : ℚ_[p] := ((η γ : ℤ_[p]) : ℚ_[p])
    have hq : algebraMap ℚ_[p] ℂ_[p] q = ((algebraMap ℚ_[p] (PadicAlgCl p) q : PadicAlgCl p) : ℂ_[p]) :=
      rfl
    have hqk : algebraMap ℚ_[p] (PadicAlgCl p) q ∈ k' := k'.algebraMap_mem q
    have hγx : γ • x ∈ closureInCp E := smul_mem_closureInCp γ (hmapsE γ) hxc
    have key : extendToClosure E (normTrace (M n)) x =
        algebraMap ℚ_[p] ℂ_[p] q * extendToClosure E (normTrace (M n)) x := by
      conv_lhs => rw [← hx γ]
      rw [hq, extendToClosure_mul (hadd n) (hbd n hn) hkE hmul hqk hγx,
        extendToClosure_smul (hadd n) (hbd n hn) γ (hmapsE γ) (fun y _ => hcomm γ n y) hxc, ← hbx,
        gal_smul_coe, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hγ b ((mem_restrictScalars _).1 hb)]
    have hq1 : algebraMap ℚ_[p] ℂ_[p] q ≠ 1 := by
      rw [Ne, ← map_one (algebraMap ℚ_[p] ℂ_[p]), (algebraMap ℚ_[p] ℂ_[p]).injective.eq_iff]
      intro h
      apply hγη
      have h' : (η γ : ℤ_[p]) = 1 := Subtype.ext (by simpa [q] using h)
      exact Units.ext h'
    have h2 : (algebraMap ℚ_[p] ℂ_[p] q - 1) * extendToClosure E (normTrace (M n)) x = 0 := by
      rw [sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hq1)

  have hbound' : ∀ ε > 0, ‖x‖ ≤ (1 + C) * ε := by
    intro ε hε
    obtain ⟨_, ⟨y, hy, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 hxc ε hε
    obtain ⟨m, hm⟩ := hmemE hy
    set m' := max m n₁
    have hym : y ∈ M m' := hM (le_max_left _ _) hm
    have hyc : (y : ℂ_[p]) ∈ closureInCp E := coe_mem_closureInCp hy
    have hsub : (y : ℂ_[p]) - x ∈ closureInCp E := sub_mem_closureInCp hyc hxc
    have hadd' := hadd m'
    have hbd' := hbd m' (le_max_right _ _)
    have h1 : extendToClosure E (normTrace (M m')) (y : ℂ_[p]) =
        extendToClosure E (normTrace (M m')) ((y : ℂ_[p]) - x) +
          extendToClosure E (normTrace (M m')) x := by
      rw [extendToClosure_sub hadd' hbd' hyc hxc]
      ring
    rw [extendToClosure_coe hadd' hbd' hy, normTrace_of_mem _ hym, hR m' (le_max_right _ _),
      add_zero] at h1
    have h2 : ‖(y : ℂ_[p])‖ ≤ C * ε := by
      rw [h1]
      refine (norm_extendToClosure_le hadd' hbd' hsub).trans ?_
      rw [← dist_eq_norm, dist_comm]
      exact mul_le_mul_of_nonneg_left hxy.le hC0
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - (y : ℂ_[p])‖ + ‖(y : ℂ_[p])‖ := norm_add_le _ _
      _ ≤ ε + C * ε := add_le_add (by rw [← dist_eq_norm]; exact hxy.le) h2
      _ = (1 + C) * ε := by ring
  by_contra hx0
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have h := hbound' (‖x‖ / (2 * (1 + C))) (by positivity)
  have h' : (1 + C) * (‖x‖ / (2 * (1 + C))) = ‖x‖ / 2 := by
    field_simp
  rw [h'] at h
  linarith
end GroundTheory.PAdicHodge.SenTateChar
