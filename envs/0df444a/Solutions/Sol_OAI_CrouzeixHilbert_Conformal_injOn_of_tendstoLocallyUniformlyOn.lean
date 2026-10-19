-- Prove2me | solution 1 for OAI.CrouzeixHilbert.Conformal.injOn_of_tendstoLocallyUniformlyOn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-19T00:34:26.195602+00:00
-- url     : https://prove2.me/submissions/e3690e94-d433-4ad2-bbdd-4677f67d22f9

import Mathlib
import Theorems.Thm_OAI_CrouzeixHilbert_Conformal_zero_or_ne_of_tendstoLocallyUniformlyOn

section
-- module Solutions.OAIQW_CrouzeixHilbert.Hurwitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hurwitz. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

theorem injOn_of_tendstoLocallyUniformlyOn_oai {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (hlim : TendstoLocallyUniformlyOn F f l U)
    (hd : ∀ i, DifferentiableOn ℂ (F i) U) (hi : ∀ i, InjOn (F i) U)
    (hnc : ¬ ∃ c, EqOn f (fun _ => c) U) : InjOn f U := by
  intro a ha b hb hab
  by_contra hne
  have hnb : a ∈ U ∩ {b}ᶜ := ⟨ha, hne⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (hU.inter isClosed_singleton.isOpen_compl) a hnb
  have hsubU : ball a r ⊆ U := fun _ hz => (hsub hz).1
  have hl : TendstoLocallyUniformlyOn (fun i z => F i z - F i b)
      (fun z => f z - f b) l (ball a r) := by
    have hconst := ((hlim.tendsto_at hb).tendstoUniformlyOn_const (s := ball a r)).tendstoLocallyUniformlyOn
    exact (uniformContinuous_fst.sub uniformContinuous_snd).comp_tendstoLocallyUniformlyOn
      ((hlim.mono hsubU).prodMk hconst)
  have hdz : ∀ i, DifferentiableOn ℂ (fun z => F i z - F i b) (ball a r) :=
    fun i => ((hd i).mono hsubU).sub_const _
  have hzero : ∀ i z, z ∈ ball a r → F i z - F i b ≠ 0 := by
    intro i z hz he
    exact (hsub hz).2 (hi i (hsubU hz) hb (sub_eq_zero.mp he))
  rcases zero_or_ne_of_tendstoLocallyUniformlyOn isOpen_ball (convex_ball a r).isPreconnected
      hl hdz hzero with he | hn
  · apply hnc
    refine ⟨f b, ?_⟩
    apply (hlim.differentiableOn (Eventually.of_forall hd) hU).analyticOnNhd hU
      |>.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hc ha
    filter_upwards [ball_mem_nhds a hr] with z hz
    exact sub_eq_zero.mp (he hz)
  · exact hn a (mem_ball_self hr) (sub_eq_zero.mpr hab)

end CrouzeixHilbert.Conformal

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CrouzeixHilbert.Conformal.injOn_of_tendstoLocallyUniformlyOn_oai.{u_1} := @OAI.CrouzeixHilbert.Conformal.injOn_of_tendstoLocallyUniformlyOn_oai.{u_1}
