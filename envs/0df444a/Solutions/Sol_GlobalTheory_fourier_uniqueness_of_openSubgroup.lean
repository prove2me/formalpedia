-- Prove2me | solution 1 for GlobalTheory.fourier_uniqueness_of_openSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:58:58.588032+00:00
-- url     : https://prove2.me/submissions/6d3b3f41-93eb-4372-b32c-0a7b49a25db0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierUniquenessOfOpenSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
open MeasureTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ {H A : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsAddHaarMeasure] [AddCommGroup A] (χ : A → H → ℂ), (∀ a s t, χ a (s + t) = χ a s * χ a t) → (∀ a, χ a 0 = 1) → (∀ t, χ 0 t = 1) → (∀ a b t, χ (a + b) t = χ a t * χ b t) → ∀ L : AddSubgroup H, IsOpen (L : Set H) → (∀ x, x ∉ L → ∃ a, (∀ l ∈ L, χ a l = 1) ∧ χ a x ≠ 1) → ∀ (φ : H → ℂ) (Kc : Set H), IsCompact Kc → (∀ t, t ∉ Kc → φ t = 0) → (∀ t, ∀ l ∈ L, φ (t + l) = φ t) → (∀ a, (∀ l ∈ L, χ a l = 1) → ∫ t, χ a t * φ t ∂μ = 0) → φ = 0 := by
  intro H A _ _ _ _ _ μ _ _ χ hs ha0 h0t hadd L hL hsep φ Kc hK hsupp hφL hint
  by_contra hφ
  obtain ⟨t₀, ht₀⟩ : ∃ t, φ t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (funext h)
  have hχne : ∀ a s, χ a s ≠ 0 := fun a s h => by
    have := hs a s (-s)
    rw [add_neg_cancel, ha0, h, zero_mul] at this
    exact one_ne_zero this
  haveI : DiscreteTopology (H ⧸ L) := QuotientAddGroup.discreteTopology hL
  have hTfin : (QuotientAddGroup.mk '' Kc : Set (H ⧸ L)).Finite :=
    (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete
  let r : H ⧸ L → H := Quotient.out
  have hr : ∀ t : H, ∃ l ∈ L, r (t : H ⧸ L) = t + l := fun t => by
    obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add L t
    exact ⟨l, l.2, hl⟩
  have hmkr : ∀ q : H ⧸ L, ((r q : H) : H ⧸ L) = q := fun q => Quotient.out_eq q
  have hpre : ∀ q : H ⧸ L, (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) : Set H) =
      (fun h => -r q + h) ⁻¹' (L : Set H) := by
    intro q
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    conv_lhs => rw [← hmkr q]
    rw [eq_comm]
    exact QuotientAddGroup.eq
  have hmeas : ∀ q : H ⧸ L, μ (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L))) = μ L := by
    intro q
    rw [hpre, measure_preimage_add]
  have hmset : ∀ q : H ⧸ L, MeasurableSet (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L))) := by
    intro q
    rw [hpre]
    exact (hL.preimage (continuous_add_left (-r q))).measurableSet
  have hLtop : μ L < ⊤ := by
    have hsub : (QuotientAddGroup.mk ⁻¹' ({(t₀ : H ⧸ L)} : Set (H ⧸ L))) ⊆ Kc := by
      intro x hx
      by_contra hxK
      have hx' : -t₀ + x ∈ L := QuotientAddGroup.eq.mp hx.symm
      have := hφL t₀ _ hx'
      rw [add_neg_cancel_left, hsupp x hxK] at this
      exact ht₀ this.symm
    rw [← hmeas (t₀ : H ⧸ L)]
    exact (measure_mono hsub).trans_lt hK.measure_lt_top
  have hLpos : 0 < μ.real L := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hL.measure_pos μ ⟨0, L.zero_mem⟩).ne' hLtop.ne
  have hχL : ∀ a, (∀ l ∈ L, χ a l = 1) → ∀ t l, l ∈ L → χ a (t + l) = χ a t := by
    intro a ha t l hl
    rw [hs, ha l hl, mul_one]
  have hsum : ∀ a, (∀ l ∈ L, χ a l = 1) →
      ∑ q ∈ hTfin.toFinset, χ a (r q) * φ (r q) = 0 := by
    intro a ha
    have hpt : (fun t => χ a t * φ t) = fun t => ∑ q ∈ hTfin.toFinset,
        (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L))).indicator
          (fun _ => χ a (r q) * φ (r q)) t := by
      funext t
      obtain ⟨l, hl, hrt⟩ := hr t
      by_cases htT : (t : H ⧸ L) ∈ (QuotientAddGroup.mk '' Kc : Set (H ⧸ L))
      · rw [Finset.sum_eq_single (t : H ⧸ L)]
        · rw [Set.indicator_of_mem (show t ∈ QuotientAddGroup.mk ⁻¹' ({(t : H ⧸ L)} : Set (H ⧸ L)) from rfl), hrt, hχL a ha t l hl, hφL t l hl]
        · intro q _ hq
          exact Set.indicator_of_notMem (show t ∉ QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) from
            fun h => hq (Set.mem_singleton_iff.mp h).symm) _
        · intro h
          exact absurd (hTfin.mem_toFinset.mpr htT) h
      · have htK : t ∉ Kc := fun h => htT ⟨t, h, rfl⟩
        rw [hsupp t htK, mul_zero]
        symm
        refine Finset.sum_eq_zero fun q hq => Set.indicator_of_notMem
          (show t ∉ QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) from fun h => htT ?_) _
        rw [show (t : H ⧸ L) = q from Set.mem_singleton_iff.mp h]
        exact hTfin.mem_toFinset.mp hq
    have hI := hint a ha
    rw [hpt, integral_finset_sum] at hI
    · simp_rw [integral_indicator_const _ (hmset _), measureReal_def, hmeas,
        ← measureReal_def] at hI
      rw [← Finset.smul_sum] at hI
      exact (smul_eq_zero.mp hI).resolve_left hLpos.ne'
    · intro q _
      refine IntegrableOn.integrable_indicator ?_ (hmset q)
      exact integrableOn_const (by rw [hmeas]; exact hLtop.ne)
  let A' : AddSubmonoid A :=
    { carrier := {a | ∀ l ∈ L, χ a l = 1}
      zero_mem' := fun l _ => h0t l
      add_mem' := fun {a b} ha hb l hl => by rw [hadd, ha l hl, hb l hl, mul_one] }
  let f : H ⧸ L → (Multiplicative A' →* ℂ) := fun q =>
    { toFun := fun g => χ ((Multiplicative.toAdd g : A') : A) (r q)
      map_one' := h0t _
      map_mul' := fun g g' => hadd _ _ _ }
  have hfinj : Function.Injective f := by
    intro q q' hqq
    by_contra hne
    have hx : r q - r q' ∉ L := by
      intro hx
      apply hne
      rw [← hmkr q, ← hmkr q']
      refine QuotientAddGroup.eq.mpr ?_
      have := L.neg_mem hx
      rwa [neg_sub, ← neg_add_eq_sub] at this
    obtain ⟨a, ha, hax⟩ := hsep _ hx
    have hval := DFunLike.congr_fun hqq (Multiplicative.ofAdd (⟨a, ha⟩ : A'))
    change χ a (r q) = χ a (r q') at hval
    apply hax
    have e : χ a (r q) = χ a (r q - r q') * χ a (r q') := by rw [← hs, sub_add_cancel]
    rw [hval] at e
    exact mul_right_cancel₀ (hχne a (r q')) (by rw [one_mul]; exact e.symm)
  have hli : LinearIndependent ℂ
      (fun q : hTfin.toFinset => (f q : Multiplicative A' → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative A') ℂ).comp (fun q : hTfin.toFinset => f q)
      (hfinj.comp Subtype.val_injective)
  have hzero := Fintype.linearIndependent_iff.mp hli (fun q => φ (r q)) (by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h := hsum _ (Multiplicative.toAdd g).2
    rw [← Finset.sum_coe_sort] at h
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h
    exact mul_comm _ _)
  have ht₀T : (t₀ : H ⧸ L) ∈ hTfin.toFinset :=
    hTfin.mem_toFinset.mpr ⟨t₀, by_contra fun h => ht₀ (hsupp t₀ h), rfl⟩
  have h0 := hzero ⟨_, ht₀T⟩
  obtain ⟨l, hl, hrt⟩ := hr t₀
  change φ (r (t₀ : H ⧸ L)) = 0 at h0
  rw [hrt, hφL t₀ l hl] at h0
  exact ht₀ h0
end _root_.GlobalTheory
end GlobalTheory
