-- Prove2me | solution 1 for GlobalTheory.RegularElementQuotient.exists_isRegular_quotSMulTop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:15:39.202335+00:00
-- url     : https://prove2.me/submissions/023e47cc-b849-403c-b74b-103e6f4c84ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Theorems.Thm_GlobalTheory_RegularElementQuotient_maximalIdeal_smul_top_lt_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open CategoryTheory Abelian Limits RingTheory.Sequence Pointwise
open GlobalTheory GlobalTheory.RegularElementQuotient
namespace GlobalTheory.RegularElementQuotient
theorem _root_.solution {R : Type u_1} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [Small.{u_2, u_1} R] {M : Type u_2} [AddCommGroup M] [Module R M]
    [Module.Finite R M] {xs : List R} (hxs : IsRegular M xs) {n : ℕ}
    (hn : n + 1 ≤ xs.length) {y : R} (hy : y ∈ IsLocalRing.maximalIdeal R)
    (hreg : IsSMulRegular M y) :
    ∃ zs : List R, zs.length = n ∧ IsRegular (QuotSMulTop y M) zs := by
  set 𝔪 := IsLocalRing.maximalIdeal R

  have : Nontrivial M :=
    (Submodule.nontrivial_iff R).mp (nontrivial_of_ne _ _ hxs.top_ne_smul)

  have hmem : ∀ x ∈ xs, x ∈ 𝔪 := by
    intro x hx
    by_contra hx𝔪
    have hu : IsUnit x := by
      by_contra hnu
      exact hx𝔪 ((IsLocalRing.mem_maximalIdeal x).mpr hnu)
    have htop : Ideal.ofList xs = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span hx) hu
    apply hxs.top_ne_smul
    rw [htop, Submodule.top_smul]

  have : Nontrivial (QuotSMulTop y M) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    refine ne_top_of_le_ne_top (maximalIdeal_smul_top_lt_top (R := R) M).ne ?_
    rw [← Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hy)
  have hltM : 𝔪 • (⊤ : Submodule R M) < ⊤ := maximalIdeal_smul_top_lt_top M
  have hltQ : 𝔪 • (⊤ : Submodule R (QuotSMulTop y M)) < ⊤ :=
    maximalIdeal_smul_top_lt_top (QuotSMulTop y M)

  have hM := (ModuleCat.exists_isRegular_tfae 𝔪 xs.length (ModuleCat.of R M) hltM).out 3 1
  have hExtM := hM.mp ⟨xs, rfl, hmem, hxs⟩

  have hS := IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) hreg
  have hExtQ : ∀ i < n, Subsingleton (Abelian.Ext
      (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪))) (ModuleCat.of R (QuotSMulTop y M)) i) := by
    intro i hi
    have hE := Abelian.Ext.covariant_sequence_exact₃'
      (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪))) hS i (i + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at hE
    have h0 := hExtM i (by omega)
    have h1 := hExtM (i + 1) (by omega)
    have key : ∀ x : Abelian.Ext (ModuleCat.of R (Shrink.{u_2} (R ⧸ 𝔪)))
        (ModuleCat.of R (QuotSMulTop y M)) i, x = 0 := by
      intro x
      obtain ⟨w, hw⟩ := (hE x).mp (h1.elim _ _)
      rw [← hw, h0.elim w 0]
      exact map_zero _
    exact ⟨fun a b => by rw [key a, key b]⟩

  have hQ := (ModuleCat.exists_isRegular_tfae 𝔪 n
    (ModuleCat.of R (QuotSMulTop y M)) hltQ).out 1 3
  obtain ⟨zs, hlen, -, hzs⟩ := hQ.mp hExtQ
  exact ⟨zs, hlen, hzs⟩
end GlobalTheory.RegularElementQuotient
