-- Prove2me | solution 1 for GlobalTheory.PowerIdealSurjectivity.aeval_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:43:49.302792+00:00
-- url     : https://prove2.me/submissions/eb2c9ed5-fd14-4333-a633-acc6eebf2a22

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanSubMemSq
import Theorems.Thm_GlobalTheory_PowerIdealSurjectivity_exists_span_sub_mem_sq
import Theorems.Thm_GlobalTheory_PowerIdealSurjectivity_exists_sub_mem_pow
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply



set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerIdealSurjectivity
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
namespace GlobalTheory.PowerIdealSurjectivity
theorem _root_.solution (O A : Type) [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A]
    [Module.Finite O A] [IsLocalRing A] (q : O) (hq : q ∈ IsLocalRing.maximalIdeal O)
    (ε : A →ₐ[O] O) (d : ℕ) (x : Fin d → A) (hx : ∀ i, ε (x i) = 0)
    (hN : ∀ i, ∃ N : ℕ, algebraMap O A q ∣ x i ^ N)
    (hs : Submodule.span O (Set.range fun i ↦ GlobalTheory.AugCot.d ε (x i)) = ⊤) :
    Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin d) O → A) := by
  classical
  let B : Subalgebra O A := Algebra.adjoin O (Set.range x)
  have h0 : ∀ a, ∃ b ∈ B, a - b ∈ RingHom.ker ε := fun a =>
    ⟨algebraMap O A (ε a), B.algebraMap_mem _,
      RingHom.mem_ker.mpr (show ε (a - algebraMap O A (ε a)) = 0 by simp)⟩
  have h1 : ∀ c ∈ RingHom.ker ε, ∃ m ∈ B, m ∈ RingHom.ker ε ∧ c - m ∈ RingHom.ker ε ^ 2 := by
    intro c hc
    obtain ⟨m, hm, hmI, hcm⟩ := exists_span_sub_mem_sq ε x hx hs hc
    exact ⟨m, Algebra.span_le_adjoin O _ hm, hmI, hcm⟩

  let φ : A →ₗ[O] A := LinearMap.id - (Algebra.linearMap O A) ∘ₗ ε.toLinearMap
  have hφ : ∀ a, φ a = a - algebraMap O A (ε a) := fun a => rfl
  have hfg : (RingHom.ker ε).FG := by
    apply Submodule.FG.of_restrictScalars O
    have heq : (RingHom.ker ε).restrictScalars O = LinearMap.range φ := by
      ext c
      rw [Submodule.restrictScalars_mem, LinearMap.mem_range]
      constructor
      · intro hc
        refine ⟨c, ?_⟩
        rw [hφ, show ε c = 0 from RingHom.mem_ker.mp hc, map_zero, sub_zero]
      · rintro ⟨a, rfl⟩
        rw [hφ]
        exact RingHom.mem_ker.mpr (show ε (a - algebraMap O A (ε a)) = 0 by simp)
    rw [heq, ← Submodule.map_top]
    exact (Module.Finite.fg_top (R := O) (M := A)).map φ

  have hker_ne : RingHom.ker ε ≠ ⊤ := RingHom.ker_ne_top ε
  have hle_span : RingHom.ker ε ≤ Ideal.span (Set.range x) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := RingHom.ker ε) hfg ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal hker_ne
    · intro c hc
      obtain ⟨m, hm, -, hcm⟩ := exists_span_sub_mem_sq ε x hx hs hc
      have hm' : m ∈ Ideal.span (Set.range x) := Submodule.span_le_restrictScalars O A _ hm
      rw [pow_two, ← smul_eq_mul] at hcm
      rw [show c = m + (c - m) by ring]
      exact Submodule.add_mem_sup hm' hcm

  have hrad : Ideal.span (Set.range x) ≤ (Ideal.span {algebraMap O A q}).radical := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨N, hNi⟩ := hN i
    exact ⟨N, Ideal.mem_span_singleton.mpr hNi⟩
  have hfgx : (Ideal.span (Set.range x)).FG :=
    ⟨Finset.univ.image x, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
  obtain ⟨K, hK⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hfgx

  have htop : (⊤ : Submodule O A) ≤ Subalgebra.toSubmodule B := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O)
      Module.Finite.fg_top ?_ ?_
    · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    · intro a _
      obtain ⟨b, hb, hab⟩ := exists_sub_mem_pow B (RingHom.ker ε) h0 h1 K a
      have h2 : a - b ∈ Ideal.span (Set.range x) ^ K :=
        Ideal.pow_right_mono hle_span K (Ideal.pow_le_pow_right (Nat.le_succ K) hab)
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hK h2)
      have h3 : a - b ∈ IsLocalRing.maximalIdeal O • (⊤ : Submodule O A) := by
        rw [← hy, mul_comm, ← Algebra.smul_def]
        exact Submodule.smul_mem_smul hq Submodule.mem_top
      rw [show a = b + (a - b) by ring]
      exact Submodule.add_mem_sup hb h3
  intro a
  have ha : a ∈ B := htop Submodule.mem_top
  rw [show B = (MvPolynomial.aeval x).range from Algebra.adjoin_range_eq_range_aeval O x] at ha
  obtain ⟨p, hp⟩ := ha
  exact ⟨p, hp⟩
end GlobalTheory.PowerIdealSurjectivity
