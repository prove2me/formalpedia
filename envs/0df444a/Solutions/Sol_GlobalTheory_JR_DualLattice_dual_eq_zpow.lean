-- Prove2me | solution 1 for GlobalTheory.JR.DualLattice.dual_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:48.029045+00:00
-- url     : https://prove2.me/submissions/95a787fe-ad2c-4b0a-b022-6515b1f9ac51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianTraceDualIntegersEqUniformizerPow
import Theorems.Thm_GlobalTheory_JR_DualLattice_eq_zpow_mul_unit
import Theorems.Thm_GlobalTheory_JR_DualLattice_eq_zpow_smul
import Theorems.Thm_GlobalTheory_JR_EtFacts_main
import Theorems.Thm_GlobalTheory_JR_EtMeas_finite_L
import Theorems.Thm_GlobalTheory_JR_EtMeas_top_facts
import Theorems.Thm_GlobalTheory_StdChar_psi_conductor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.DualLattice
set_option maxHeartbeats 1000000
namespace GlobalTheory.JR.DualLattice
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → IsField A.L → ∀ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) → (∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O) → ∀ a : A.Kˣ, ∃ e : ℤ, {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} = {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L ((ϖ ^ e : A.Kˣ) : A.K) * z} := by
  intro F E _ _ _ _ U A ψ hψ hK hL ϖ O hOo hOc hOstar hpO hpnu hdich hnbhd hex a
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hLnt : Nontrivial A.L := ⟨hL.exists_pair_ne⟩
  have hKnt : Nontrivial A.K := ⟨hK.exists_pair_ne⟩
  let p : A.Lˣ := Units.map (algebraMap A.K A.L).toMonoidHom ϖ
  have hp : (p : A.L) = algebraMap A.K A.L (ϖ : A.K) := rfl
  have hpz : ∀ v : ℤ, ((p ^ v : A.Lˣ) : A.L) = algebraMap A.K A.L ((ϖ ^ v : A.Kˣ) : A.K) := by
    intro v
    rw [show p ^ v = Units.map (algebraMap A.K A.L).toMonoidHom (ϖ ^ v) from (map_zpow _ ϖ v).symm]
    rfl
  have hpn : ∀ n : ℕ, (p : A.L) ^ n = algebraMap A.K A.L ((ϖ : A.K) ^ n) := by
    intro n; rw [hp, map_pow]

  have hmul : ∀ y ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1}, ∀ r ∈ O,
      r * y ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} := by
    intro y hy r hr m hm
    have e1 : star (r * y) * m = star y * (star r * m) := by rw [star_mul']; ring
    simp only [Et.kerL, Set.mem_setOf_eq] at hy ⊢
    rw [e1]
    exact hy _ (O.mul_mem (hOstar r hr) hm)

  have hψl : IsLocallyConstant (fun x => ψ x) := ((GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ).1
  have hg : Continuous (fun q : A.L × A.L =>
      Algebra.trace F A.K ((a : A.K) * Algebra.trace A.K A.L (star q.1 * q.2))) := by
    have hs : Continuous (star : A.L → A.L) := IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)
    have ht : Continuous (Algebra.trace A.K A.L) :=
      IsModuleTopology.continuous_of_linearMap ((Algebra.trace A.K A.L).restrictScalars F)
    have htF : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact htF.comp (continuous_const.mul (ht.comp ((hs.comp continuous_fst).mul continuous_snd)))
  have hW : IsOpen {q : A.L × A.L | A.kerL ψ (a : A.K) q.1 q.2 = 1} :=
    (hψl.isOpen_fiber 1).preimage hg
  obtain ⟨u, v, hu, -, h0u, hOv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : A.L))) hOc hW
    (by
      rintro ⟨y, m⟩ ⟨hy, -⟩
      simp only [Set.mem_singleton_iff] at hy
      subst hy
      simp [Et.kerL, Et.psiK])
  obtain ⟨n, hn⟩ := hnbhd u (hu.mem_nhds (h0u rfl))
  have hbig : ∃ n : ℕ, ∀ z ∈ O, (p : A.L) ^ n * z ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} := by
    refine ⟨n, fun z hz m hm => ?_⟩
    have : ((p : A.L) ^ n * z, m) ∈ u ×ˢ v := ⟨by rw [hpn]; exact hn z hz, hOv hm⟩
    exact huv this

  have hinj : ∀ k₁ k₂ : A.K, algebraMap A.K A.L k₁ = algebraMap A.K A.L k₂ → k₁ = k₂ := by
    intro k₁ k₂ h
    by_contra hne
    obtain ⟨k', hk'⟩ := hK.mul_inv_cancel (sub_ne_zero.2 hne)
    have : algebraMap A.K A.L ((k₁ - k₂) * k') = 0 := by rw [map_mul, map_sub, h, sub_self, zero_mul]
    rw [hk', map_one] at this
    exact one_ne_zero this
  have hne : ∃ y, y ∉ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} := by
    obtain ⟨-, x, hx, -⟩ := hψ
    have hd : (Module.finrank F A.K : F) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    set t : F := x / (2 * (Module.finrank F A.K : F)) with ht
    set c : A.K := ((a⁻¹ : A.Kˣ) : A.K) * algebraMap F A.K t with hc
    refine ⟨algebraMap A.K A.L c, fun h => hx ?_⟩
    have h1 := h 1 (one_mem O)
    have htr : Algebra.trace A.K A.L (star (algebraMap A.K A.L c) * 1) = 2 * c := by
      apply hinj
      rw [mul_one, A.star_K, (GlobalTheory.JR.EtFacts.main F E A).2.1, A.star_K, two_mul, map_add]
    have hac : (a : A.K) * (2 * c) = algebraMap F A.K (2 * t) := by
      rw [hc, map_mul, map_ofNat, ← mul_assoc, mul_comm (a : A.K) 2, mul_assoc 2, ← mul_assoc (a : A.K),
        Units.mul_inv, one_mul]
    simp only [Et.kerL, Et.psiK, htr, hac, Algebra.trace_algebraMap, nsmul_eq_mul] at h1
    rw [← h1, ht]
    congr 1
    field_simp

  have hsep : ∀ x : A.L, x ≠ 0 → ∃ n : ℕ, ∀ z ∈ O, (p : A.L) ^ n * z ≠ x := by
    intro x hx
    obtain ⟨n, hn⟩ := hnbhd {x}ᶜ (isOpen_compl_singleton.mem_nhds (Ne.symm hx))
    exact ⟨n, fun z hz => by rw [hpn]; exact hn z hz⟩
  have hex' : ∀ y : A.L, ∃ n : ℕ, (p : A.L) ^ n * y ∈ O := by
    intro y
    obtain ⟨n, hn⟩ := hex y
    exact ⟨n, by rw [hpn]; exact hn⟩
  have hdich' : ∀ y ∈ O, (∃ z ∈ O, y = (p : A.L) * z) ∨ ∃ z ∈ O, y * z = 1 := by
    rw [hp]; exact hdich
  have hunit := eq_zpow_mul_unit O p hdich' hsep hex'
  obtain ⟨e, he⟩ := eq_zpow_smul O p _ (by rw [hp]; exact hpO) hmul hbig hne hex' hunit
  refine ⟨e, ?_⟩
  rw [he]
  simp only [hpz]
end GlobalTheory.JR.DualLattice
