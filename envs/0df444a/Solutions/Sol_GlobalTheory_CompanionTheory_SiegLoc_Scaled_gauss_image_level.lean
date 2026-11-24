-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:44:30.446531+00:00
-- url     : https://prove2.me/submissions/4e351ae3-ae48-4d96-b65a-eec7522bb95a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumCompSurj
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardRangeMulQuotientBoundedLevel
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_Scaled_sum_comp_surj
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_Scaled_fixed_decomp
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_Scaled_unit_notMem
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_Scaled_card_range_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_mem_lev_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_psi_pow
import Theorems.Thm_GlobalTheory_T_unramified_quotient_card
import Theorems.Thm_UpperTheory_Reformulated_B_Rd1_sum_comp_surj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.Scaled
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.SiegLoc.Scaled
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → (∀ (j : ℕ) (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w))) = ((ε : ℂ) * q) ^ j) → ∀ (k : ℕ) (d : R), σ d = d → ∃ e : ℕ, e ≤ k ∧ Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) = (q ^ 2) ^ e ∧ ∀ a : R, σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ k, ψ k (Ideal.Quotient.mk (lev ϖ k) (a * d) * (barσ σ ϖ hR.fix_ϖ k w * w))) = (q : ℂ) ^ (2 * k) * ((ε : ℂ) / q) ^ e := by
  intro R _ σ ϖ q ε hR _ ψ hψ H k d hd
  have hq : (q : ℂ) ≠ 0 := by
    have : q ≠ 0 := by have := hR.one_lt; omega
    exact_mod_cast this
  have hcard : ∀ j, Fintype.card (R ⧸ lev ϖ j) = q ^ (2 * j) := fun j => by
    rw [← Nat.card_eq_fintype_card]
    exact GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR j
  rcases fixed_decomp hR k d hd with h0 | ⟨a₀, e, c, rfl, hc, hc1, rfl⟩
  · have hz : Ideal.Quotient.mk (lev ϖ k) d = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h0
    refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · have : (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) = {0} := by
        ext z
        simp [hz, eq_comm]
      rw [this]
      simp
    · intro a _ _
      have hz' : Ideal.Quotient.mk (lev ϖ k) (a * d) = 0 := by rw [map_mul, hz, mul_zero]
      simp only [hz', zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ,
        hcard, nsmul_eq_mul, mul_one, pow_zero]
      push_cast
      rfl
  · have hcu : IsUnit c := hR.fixLocal c hc hc1
    refine ⟨e, by omega, ?_, ?_⟩
    · rw [card_range_mul hR.reg hcu e a₀, GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR e, pow_mul]
    · intro a ha ha1
      have hau : IsUnit a := hR.fixLocal a ha ha1
      have hac : a * c ∉ lev ϖ 1 := unit_notMem hR.notUnit (hau.mul hcu)
      have hacf : σ (a * c) = a * c := by rw [map_mul, ha, hc]
      have hle : lev ϖ (e + a₀) ≤ lev ϖ e := by
        intro x hx
        obtain ⟨t, rfl⟩ := mem_lev_iff.1 hx
        exact mem_lev_iff.2 ⟨ϖ ^ a₀ * t, by rw [pow_add]; ring⟩
      let π : (R ⧸ lev ϖ (e + a₀)) →+ (R ⧸ lev ϖ e) :=
        (Ideal.Quotient.factor hle).toAddMonoidHom
      have hπ : Function.Surjective π := by
        intro x
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact ⟨Ideal.Quotient.mk _ y, rfl⟩
      let G : R ⧸ lev ϖ e → ℂ := fun v =>
        ψ e (Ideal.Quotient.mk (lev ϖ e) (a * c) * (barσ σ ϖ hR.fix_ϖ e v * v))
      have hF : ∀ w : R ⧸ lev ϖ (e + a₀),
          ψ (e + a₀) (Ideal.Quotient.mk (lev ϖ (e + a₀)) (a * (ϖ ^ a₀ * c)) *
            (barσ σ ϖ hR.fix_ϖ (e + a₀) w * w)) = G (π w) := by
        intro w
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
        have h1 := psi_pow hψ e a₀ (a * c * (σ y * y))
        change ψ (e + a₀) (Ideal.Quotient.mk _ (a * (ϖ ^ a₀ * c)) *
            (Ideal.Quotient.mk _ (σ y) * Ideal.Quotient.mk _ y)) =
          ψ e (Ideal.Quotient.mk _ (a * c) *
            (Ideal.Quotient.mk _ (σ y) * Ideal.Quotient.mk _ y))
        rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← h1]
        congr 2
        ring
      rw [Finset.sum_congr rfl (fun w _ => hF w)]
      have h2 := sum_comp_surj π hπ G
      have h3 : ∑ v, G v = ((ε : ℂ) * q) ^ e := H e (a * c) hacf hac
      rw [h3, hcard, hcard] at h2
      push_cast at h2
      have hqe : (q : ℂ) ^ (2 * e) ≠ 0 := pow_ne_zero _ hq
      have h4 : ∑ w, G (π w) =
          (q : ℂ) ^ (2 * (e + a₀)) * ((ε : ℂ) * q) ^ e / (q : ℂ) ^ (2 * e) := by
        rw [← h2]
        field_simp
      rw [h4, mul_pow, div_pow]
      field_simp
      ring
end GlobalTheory.CompanionTheory.SiegLoc.Scaled
