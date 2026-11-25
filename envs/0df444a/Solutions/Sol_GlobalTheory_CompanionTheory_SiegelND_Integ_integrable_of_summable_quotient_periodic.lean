-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_of_summable_quotient_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:36:52.890952+00:00
-- url     : https://prove2.me/submissions/dc2acca6-262b-4535-b360-38a513defe9c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SummableOverLatticeQuotientLocallyConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ
namespace GlobalTheory.CompanionTheory.SiegelND.Integ
theorem _root_.solution :
    ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] (ν : Measure G) [ν.IsAddHaarMeasure] (U : AddSubgroup G),
    IsOpen (U : Set G) → IsCompact (U : Set G) → ∀ ι : H →+ G, (∀ g, ∃ h, g - ι h ∈ U) →
    ∀ f : G → ℂ, (∀ g, ∀ u ∈ U, f (g + u) = f g) →
    Summable (fun x : H ⧸ U.comap ι => ‖f (ι (Quotient.out x))‖) → Integrable f ν := by
  intro G H _ _ _ _ _ _ _ ν _ U hUo hUc ι hι f hf hs
  let r : H ⧸ U.comap ι → G := fun x => ι (Quotient.out x)
  let c : H ⧸ U.comap ι → Set G := fun x => (fun g => g - r x) ⁻¹' (U : Set G)
  have hcopen : ∀ x, IsOpen (c x) := fun x => hUo.preimage (by fun_prop)
  have hcov : ⋃ x, c x = univ := by
    refine eq_univ_of_forall fun g => mem_iUnion.2 ?_
    obtain ⟨h, hh⟩ := hι g
    refine ⟨(QuotientAddGroup.mk h : H ⧸ U.comap ι), ?_⟩
    have h1 : -h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι) ∈ U.comap ι :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
    have h2 : ι (-h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι)) ∈ U := h1
    have h3 := U.sub_mem hh h2
    have h4 : g - ι h - ι (-h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι))
        = g - r (QuotientAddGroup.mk h : H ⧸ U.comap ι) := by
      simp only [r, map_add, map_neg]; abel
    change g - r _ ∈ U
    rwa [h4] at h3
  have hdisj : Pairwise (Function.onFun Disjoint c) := by
    intro x y hxy
    refine Set.disjoint_left.2 fun g hgx hgy => hxy ?_
    have hgx' : g - r x ∈ U := hgx
    have hgy' : g - r y ∈ U := hgy
    have h1 : ι (-Quotient.out x + Quotient.out y) ∈ U := by
      have h3 := U.sub_mem hgx' hgy'
      have h4 : g - r x - (g - r y) = ι (-Quotient.out x + Quotient.out y) := by
        simp only [r, map_add, map_neg]; abel
      rwa [h4] at h3
    have h2 : (QuotientAddGroup.mk (Quotient.out x) : H ⧸ U.comap ι) = QuotientAddGroup.mk (Quotient.out y) :=
      QuotientAddGroup.eq.2 h1
    rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h2
  have hne : ∀ x, (c x).Nonempty := fun x => ⟨r x, by
    change r x - r x ∈ U
    simp⟩
  have hcount : Countable (H ⧸ U.comap ι) := by
    have hinj : Function.Injective c := by
      intro x y hxy
      by_contra hne'
      obtain ⟨g, hg⟩ := hne x
      exact Set.disjoint_left.1 (hdisj hne') hg (hxy ▸ hg)
    have hpd : (range c).PairwiseDisjoint id := by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
      exact hdisj (fun h => hxy (by rw [h]))
    have := hpd.countable_of_isOpen (by rintro _ ⟨x, rfl⟩; exact hcopen x)
      (by rintro _ ⟨x, rfl⟩; exact hne x)
    have := this.to_subtype
    exact Function.Injective.countable (f := Set.rangeFactorization c)
      (fun x y h => hinj (congrArg Subtype.val h))
  have hconst : ∀ x, ∀ g ∈ c x, f g = f (r x) := by
    intro x g hg
    have := hf (r x) (g - r x) hg
    rw [← this]; congr 1; abel
  have hcont : Continuous f := by
    refine IsLocallyConstant.continuous ?_
    refine (IsLocallyConstant.iff_exists_open f).2 fun g => ?_
    refine ⟨(fun y => y - g) ⁻¹' (U : Set G), hUo.preimage (by fun_prop), by simp, ?_⟩
    intro y hy
    have := hf g (y - g) hy
    rw [← this]; congr 1; abel
  have hmeas : ∀ x, ν (c x) = ν (U : Set G) := by
    intro x
    have : c x = (fun g => g + (- r x)) ⁻¹' (U : Set G) := by
      ext g; simp [c, sub_eq_add_neg]
    rw [this, measure_preimage_add_right]
  have hUfin : ν (U : Set G) < ⊤ := hUc.measure_lt_top
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hsum : ∑' x, ‖f (r x)‖ₑ < ⊤ := by
    have h1 : ∑' x, ‖f (r x)‖ₑ = ∑' x, ENNReal.ofReal ‖f (r x)‖ := by
      simp [ofReal_norm_eq_enorm]
    rw [h1]
    exact hs.tsum_ofReal_lt_top
  have hint : ∫⁻ g, ‖f g‖ₑ ∂ν = (∑' x, ‖f (r x)‖ₑ) * ν (U : Set G) := by
    calc ∫⁻ g, ‖f g‖ₑ ∂ν = ∫⁻ g in ⋃ x, c x, ‖f g‖ₑ ∂ν := by rw [hcov, Measure.restrict_univ]
      _ = ∑' x, ∫⁻ g in c x, ‖f g‖ₑ ∂ν :=
          lintegral_iUnion (fun x => (hcopen x).measurableSet) hdisj _
      _ = ∑' x, ‖f (r x)‖ₑ * ν (U : Set G) := by
          refine tsum_congr fun x => ?_
          rw [setLIntegral_congr_fun (hcopen x).measurableSet
            (g := fun _ => ‖f (r x)‖ₑ) (fun g hg => by simp only [hconst x g hg]),
            setLIntegral_const, hmeas]
      _ = (∑' x, ‖f (r x)‖ₑ) * ν (U : Set G) := ENNReal.tsum_mul_right
  change ∫⁻ g, ‖f g‖ₑ ∂ν < ⊤
  rw [hint]
  exact ENNReal.mul_lt_top hsum hUfin
end GlobalTheory.CompanionTheory.SiegelND.Integ
