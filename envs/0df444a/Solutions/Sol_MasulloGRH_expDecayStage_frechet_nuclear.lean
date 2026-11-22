-- Prove2me | solution 1 for MasulloGRH.expDecayStage_frechet_nuclear
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T18:51:43.892749+00:00
-- url     : https://prove2.me/submissions/47261149-c355-46f8-a855-1b04ee4dd5b5

import Theorems.Thm_MasulloGRH_expDecayStage_weighted_mem
import Theorems.Thm_MasulloGRH_expDecayStage_weighted_domination
import Theorems.Thm_MasulloGRH_expDecayStage_weighted_closedRange
import Theorems.Thm_MasulloGRH_schwartzBruhat_quotient_goodSubgroup_frechet_nuclear
import Theorems.Thm_MasulloGRH_isFrechet_and_isNuclear_of_countable_projective

set_option autoImplicit false

universe u

namespace StageFNAux

open MasulloGRH

/-- a countable subset of an interval dominating it from both sides -/
lemma exists_countable_between (I : Set ℝ) (hI : I.OrdConnected) :
    ∃ J : Set ℝ, J ⊆ I ∧ J.Countable ∧ ∀ a ∈ I, ∃ a₁ ∈ J, ∃ a₂ ∈ J, a₁ ≤ a ∧ a ≤ a₂ := by
  classical
  refine ⟨(I ∩ Set.range (Rat.cast : ℚ → ℝ)) ∪ ({a | IsGreatest I a} ∪ {a | IsLeast I a}),
    ?_, ?_, ?_⟩
  · rintro x (⟨hx, -⟩ | hx | hx)
    · exact hx
    · exact hx.1
    · exact hx.1
  · refine Set.Countable.union ((Set.countable_range _).mono Set.inter_subset_right) ?_
    refine Set.Countable.union (Set.Subsingleton.countable ?_) (Set.Subsingleton.countable ?_)
    · intro x hx y hy; exact hx.unique hy
    · intro x hx y hy; exact hx.unique hy
  · intro a ha
    have up : ∃ a₂ ∈ (I ∩ Set.range (Rat.cast : ℚ → ℝ)) ∪ ({a | IsGreatest I a} ∪ {a | IsLeast I a}),
        a ≤ a₂ := by
      by_cases hg : IsGreatest I a
      · exact ⟨a, Or.inr (Or.inl hg), le_rfl⟩
      · have : ∃ b ∈ I, a < b := by
          by_contra hcon
          push_neg at hcon
          exact hg ⟨ha, fun b hb => hcon b hb⟩
        obtain ⟨b, hb, hab⟩ := this
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hab
        exact ⟨q, Or.inl ⟨hI.out ha hb ⟨hq1.le, hq2.le⟩, q, rfl⟩, hq1.le⟩
    have dn : ∃ a₁ ∈ (I ∩ Set.range (Rat.cast : ℚ → ℝ)) ∪ ({a | IsGreatest I a} ∪ {a | IsLeast I a}),
        a₁ ≤ a := by
      by_cases hg : IsLeast I a
      · exact ⟨a, Or.inr (Or.inr hg), le_rfl⟩
      · have : ∃ b ∈ I, b < a := by
          by_contra hcon
          push_neg at hcon
          exact hg ⟨ha, fun b hb => hcon b hb⟩
        obtain ⟨b, hb, hab⟩ := this
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hab
        exact ⟨q, Or.inl ⟨hI.out hb ha ⟨hq1.le, hq2.le⟩, q, rfl⟩, hq2.le⟩
    obtain ⟨a₂, h₂, hle₂⟩ := up
    obtain ⟨a₁, h₁, hle₁⟩ := dn
    exact ⟨a₁, h₁, a₂, h₂, hle₁, hle₂⟩

end StageFNAux

open MasulloGRH StageFNAux in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k) :
    IsFrechet (ExpDecayStage G m I k) ∧ IsNuclear (ExpDecayStage G m I k) := by
  classical
  haveI : IsClosed (k : Set G) := hk.1
  obtain ⟨J, hJI, hJc, hbet⟩ := exists_countable_between I hI
  have hJne : J.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    obtain ⟨a₁, h₁, -⟩ := hbet a ha
    exact ⟨a₁, h₁⟩
  haveI : Countable J := hJc.to_subtype
  haveI : Nonempty J := hJne.to_subtype
  -- the weight operators, as linear maps
  let wL : ∀ a : ℝ, a ∈ I → ExpDecayStage G m I k →ₗ[ℂ] SchwartzBruhat (G ⧸ k) := fun a ha =>
    { toFun := fun y => ⟨_, expDecayStage_weighted_mem G m hm I hI hne k hk y a ha⟩
      map_add' := fun y z => by
        apply Subtype.ext
        funext x
        show ((m x.out ^ a : ℝ) : ℂ) * (y.1.1 x.out + z.1.1 x.out) =
          ((m x.out ^ a : ℝ) : ℂ) * y.1.1 x.out + ((m x.out ^ a : ℝ) : ℂ) * z.1.1 x.out
        ring
      map_smul' := fun c y => by
        apply Subtype.ext
        funext x
        show ((m x.out ^ a : ℝ) : ℂ) * (c * y.1.1 x.out) =
          c * (((m x.out ^ a : ℝ) : ℂ) * y.1.1 x.out)
        ring }
  have hw : ∀ a (ha : a ∈ I) (y : ExpDecayStage G m I k),
      ExpDecaySchwartz.weighted k a y.1 = wL a ha y := by
    intro a ha y
    have hmem := expDecayStage_weighted_mem G m hm I hI hne k hk y a ha
    apply Subtype.ext
    unfold ExpDecaySchwartz.weighted
    first
      | (erw [dif_pos hmem]; rfl)
      | (simp only [hmem, dif_pos]; rfl)
      | (split <;> [rfl; exact absurd hmem ‹_›])
  have hwf : ∀ a (ha : a ∈ I),
      (fun y : ExpDecayStage G m I k => ExpDecaySchwartz.weighted k a y.1) = wL a ha :=
    fun a ha => funext (hw a ha)
  let π : ∀ i : ULift.{u} J, ExpDecayStage G m I k →ₗ[ℂ] SchwartzBruhat (G ⧸ k) :=
    fun i => wL i.down.1 (hJI i.down.2)
  have hY := schwartzBruhat_quotient_goodSubgroup_frechet_nuclear G m hm k hk
  refine isFrechet_and_isNuclear_of_countable_projective (ULift.{u} J)
    (fun _ => SchwartzBruhat (G ⧸ k)) (fun _ => hY) (ExpDecayStage G m I k) π ?_ ?_ ?_
  · -- topology
    apply le_antisymm
    · refine le_iInf fun i => ?_
      have := iInf₂_le (f := fun (a : ℝ) (_ : a ∈ I) => TopologicalSpace.induced
        (fun ϕ : ExpDecayStage G m I k => ExpDecaySchwartz.weighted k a ϕ.1)
        (inferInstance : TopologicalSpace (SchwartzBruhat (G ⧸ k)))) i.down.1 (hJI i.down.2)
      rw [hwf _ (hJI i.down.2)] at this
      exact this
    · show (⨅ i : ULift.{u} J, TopologicalSpace.induced (π i) inferInstance) ≤
        ⨅ (a : ℝ) (_ : a ∈ I), TopologicalSpace.induced
          (fun ϕ : ExpDecayStage G m I k => ExpDecaySchwartz.weighted k a ϕ.1) inferInstance
      refine le_iInf₂ fun a ha => ?_
      obtain ⟨a₁, h₁, a₂, h₂, hle₁, hle₂⟩ := hbet a ha
      have hc := expDecayStage_weighted_domination G m hm I hI hne k hk a₁ a a₂ (hJI h₁) (hJI h₂)
        hle₁ hle₂
      rw [continuous_iff_le_induced] at hc
      refine le_trans (le_inf ?_ ?_) hc
      · have := iInf_le (fun i : ULift.{u} J => TopologicalSpace.induced (π i)
          (inferInstance : TopologicalSpace (SchwartzBruhat (G ⧸ k)))) ⟨⟨a₁, h₁⟩⟩
        rw [hwf _ (hJI h₁)]; exact this
      · have := iInf_le (fun i : ULift.{u} J => TopologicalSpace.induced (π i)
          (inferInstance : TopologicalSpace (SchwartzBruhat (G ⧸ k)))) ⟨⟨a₂, h₂⟩⟩
        rw [hwf _ (hJI h₂)]; exact this
  · -- separation
    intro y hy
    obtain ⟨j, hj⟩ := hJne
    have h0 := hy ⟨⟨j, hj⟩⟩
    have hfun : ∀ x : G ⧸ k, ((m x.out ^ j : ℝ) : ℂ) * y.1.1 x.out = 0 := fun x =>
      congrFun (congrArg Subtype.val h0) x
    apply Subtype.ext; apply Subtype.ext
    funext g
    have hout : ∃ h ∈ k, (QuotientGroup.mk g : G ⧸ k).out = g * h := by
      have := QuotientGroup.mk_out_eq_mul k g
      obtain ⟨h, hh⟩ := this
      exact ⟨h, h.2, hh⟩
    obtain ⟨h, hhk, hh⟩ := hout
    have := hfun (QuotientGroup.mk g)
    rw [hh] at this
    have hpos : ((m (g * h) ^ j : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (hm.1.pos _) j).ne'
    have hy' : y.1.1 (g * h) = 0 := (mul_eq_zero.1 this).resolve_left hpos
    have hinv : y.1.1 (g * h) = y.1.1 g := y.2 h hhk g
    rw [hinv] at hy'
    exact hy'
  · -- closed range
    have hc := expDecayStage_weighted_closedRange G m hm I hI hne k hk J hJI hbet
    have : (fun (y : ExpDecayStage G m I k) (i : ULift.{u} J) => π i y) =
        fun (y : ExpDecayStage G m I k) (j : ULift.{u} J) =>
          ExpDecaySchwartz.weighted k (j.down : ℝ) y.1 := by
      funext y i
      exact (hw _ (hJI i.down.2) y).symm
    rw [this]; exact hc
