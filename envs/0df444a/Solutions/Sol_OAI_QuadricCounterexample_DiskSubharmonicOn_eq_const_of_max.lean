-- Prove2me | solution 1 for OAI.QuadricCounterexample.DiskSubharmonicOn.eq_const_of_max
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T15:57:42.006584+00:00
-- url     : https://prove2.me/submissions/6b36a99b-1b66-4d9e-b827-bbeec1fcc003

import Mathlib
import Definitions.Def_OAIQWQC001

section
-- module Solutions.OAIQW_QuadricCounterexample.Removability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric

lemma DiskSubharmonicOn.eq_on_ball_of_max {Ω : Set ℂ} {u : ℂ → ℝ}
    (hu : DiskSubharmonicOn Ω u) {x : ℂ} (hx : x ∈ Ω) {r : ℝ} (hr : 0 < r)
    (hball : closedBall x r ⊆ Ω) (hmax : ∀ y ∈ Ω, u y ≤ u x) :
    ∀ y ∈ ball x r, u y = u x := by
  have hb : ball x r ⊆ Ω := ball_subset_closedBall.trans hball
  have hi := (hu.2 x hx r hr hball).1
  have hle : u ≤ᵐ[volume.restrict (ball x r)] fun _ ↦ u x :=
    (ae_restrict_mem measurableSet_ball).mono fun y hy ↦ hmax y (hb hy)
  have hc : IntegrableOn (fun _ : ℂ ↦ u x) (ball x r) :=
    integrableOn_const (measure_ne_top_of_subset ball_subset_closedBall
      (isCompact_closedBall x r).measure_ne_top)
  have he : (∫ y in ball x r, u y) = ∫ _ in ball x r, u x := by
    apply le_antisymm (integral_mono_ae hi hc hle)
    simpa only [setIntegral_const, measureReal_def, smul_eq_mul]
      using (hu.2 x hx r hr hball).2
  have hae := (integral_eq_iff_of_ae_le hi hc hle).mp he
  have hge := usc_ge_of_ae_ge isOpen_ball (hu.1.mono hb)
    (hae.mono fun _ h ↦ h.ge)
  intro y hy
  exact le_antisymm (hmax y (hb hy)) (hge y hy)

theorem DiskSubharmonicOn.eq_const_of_max_oai {Ω : Set ℂ} {u : ℂ → ℝ}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) (hu : DiskSubharmonicOn Ω u)
    {x : ℂ} (hx : x ∈ Ω) (hmax : ∀ y ∈ Ω, u y ≤ u x) :
    ∀ y ∈ Ω, u y = u x := by
  let : PreconnectedSpace Ω := isPreconnected_iff_preconnectedSpace.mp hconn
  let C : Set Ω := {y | u x ≤ u y}
  have hc : IsClosed C :=
    (upperSemicontinuousOn_iff_restrict.mpr hu.1).isClosed_preimage (u x)
  have ho : IsOpen C := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds y.property)
    have hey : u y = u x := le_antisymm (hmax y y.property) hy
    have he := hu.eq_on_ball_of_max y.property hr hball
      (fun z hz ↦ (hmax z hz).trans hey.ge)
    have hn : {z : Ω | (z : ℂ) ∈ ball (y : ℂ) r} ∈ 𝓝 y :=
      continuous_subtype_val.continuousAt (ball_mem_nhds (y : ℂ) hr)
    apply mem_of_superset hn
    intro z hz
    change u x ≤ u z
    rw [he z hz, hey]
  have hne : C.Nonempty := ⟨⟨x,hx⟩, by change u x ≤ u x; exact le_rfl⟩
  have heq : C = univ := (show IsClopen C from ⟨hc, ho⟩).eq_univ hne
  intro y hy
  have hh : (⟨y,hy⟩ : Ω) ∈ C := heq.symm ▸ mem_univ _
  exact le_antisymm (hmax y hy) hh

open scoped Pointwise
end QuadricCounterexample

end OAI
end

theorem solution : type_of% @OAI.QuadricCounterexample.DiskSubharmonicOn.eq_const_of_max_oai := @OAI.QuadricCounterexample.DiskSubharmonicOn.eq_const_of_max_oai
