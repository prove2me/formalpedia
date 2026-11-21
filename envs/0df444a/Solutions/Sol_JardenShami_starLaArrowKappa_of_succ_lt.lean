-- Prove2me | solution 1 for JardenShami.starLaArrowKappa_of_succ_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:48:01.983375+00:00
-- url     : https://prove2.me/submissions/d2c2c89a-e877-4eb5-a698-307771406952

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
import Theorems.Thm_JardenShami_sim_witness_mono_and_equivalence
import Theorems.Thm_JardenShami_card_simClasses_le
import Theorems.Thm_JardenShami_Kappa_card_eq_of_forall_exists_gt
import Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_eq
import Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_lt
import Theorems.Thm_JardenShami_Kappa_mk_Iic_lt
import Theorems.Thm_JardenShami_Kappa_mk_eq
import Theorems.Thm_JardenShami_Pairs_exists_eq_mk


set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
namespace JardenShami
theorem _root_.solution (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (h : Order.succ μ < κ) : StarLaArrowKappa κ μ := by
  classical
  intro C hC
  have hμ : μ < κ := (Order.lt_succ_of_not_isMax (not_isMax μ)).trans h
  have hκ0 := hκ.aleph0_le
  obtain ⟨mono, heqv⟩ := sim_witness_mono_and_equivalence κ μ hκ C hC
  have hRle := card_simClasses_le κ μ hκ C hC h
  -- some class `A` has size `κ`
  set R := Set.range fun β : Kappa κ => {γ : Kappa κ | Sim C β γ}
  let cl : Kappa κ → R := fun β => ⟨{γ | Sim C β γ}, β, rfl⟩
  obtain ⟨r, hr⟩ := Cardinal.infinite_pigeonhole_card cl κ (by rw [Kappa.mk_eq]) hκ0
    (by rw [hκ.cof_ord]; exact hRle.trans_lt hμ)
  set A : Set (Kappa κ) := cl ⁻¹' {r}
  have hAκ : #A = κ := le_antisymm ((Cardinal.mk_set_le A).trans (Kappa.mk_eq κ).le) hr
  have hAsim : ∀ y ∈ A, ∀ y' ∈ A, Sim C y y' := by
    intro y hy y' hy'
    have e : cl y = cl y' := hy.trans hy'.symm
    have e' : {γ | Sim C y γ} = {γ | Sim C y' γ} := congrArg Subtype.val e
    have : y' ∈ {γ | Sim C y' γ} := heqv.refl y'
    rw [← e'] at this
    exact this
  -- witnesses
  have hε : ∀ y y' : Kappa κ, ∃ e : Kappa κ, (y ∈ A → y' ∈ A → y < e ∧ y' < e) ∧
      ∀ (h1 : y < e) (h2 : y' < e), y ∈ A → y' ∈ A → C.color y e h1 = C.color y' e h2 := by
    intro y y'
    by_cases hy : y ∈ A ∧ y' ∈ A
    · obtain ⟨e, h1, h2, he⟩ := hAsim y hy.1 y' hy.2
      exact ⟨e, fun _ _ => ⟨h1, h2⟩, fun _ _ _ _ => he⟩
    · exact ⟨y, fun a b => absurd ⟨a, b⟩ hy, fun _ _ a b => absurd ⟨a, b⟩ hy⟩
  choose ε hεlt hεc using hε
  -- the greedy set `Y`
  obtain ⟨P, hP⟩ : ∃ P : Kappa κ → Prop, ∀ γ, P γ ↔ γ ∈ A ∧
      ∀ y y' (hyy' : y < y') (hy'γ : y' < γ), P y → P y' →
        C.color y γ (hyy'.trans hy'γ) = C.color y' γ hy'γ :=
    ⟨wellFounded_lt.fix fun γ ih => γ ∈ A ∧
      ∀ y y' (hyy' : y < y') (hy'γ : y' < γ), ih y (hyy'.trans hy'γ) → ih y' hy'γ →
        C.color y γ (hyy'.trans hy'γ) = C.color y' γ hy'γ,
      fun γ => by rw [WellFounded.fix_eq]⟩
  set Y : Set (Kappa κ) := {γ | P γ}
  have hYA : Y ⊆ A := fun γ hγ => ((hP γ).1 hγ).1
  have hYunb : ∀ x, ∃ y ∈ Y, x < y := by
    intro x
    by_contra hc
    push Not at hc
    have hYs : #Y < κ := (Cardinal.mk_le_mk_of_subset fun y hy => hc y hy).trans_lt
      (Kappa.mk_Iic_lt hκ0 x)
    let E : Set (Kappa κ) := Set.range fun q : Y × Y => ε q.1 q.2
    have hEs : #E < κ := by
      refine Cardinal.mk_range_le.trans_lt ?_
      rw [Cardinal.mk_prod, Cardinal.lift_id]
      exact Cardinal.mul_lt_of_lt hκ0 hYs hYs
    obtain ⟨z, hz⟩ := Kappa.exists_gt_of_card_lt hκ hEs
    obtain ⟨γ, hγA, hγ⟩ := Kappa.exists_gt_of_card_eq hκ0 hAκ (max x z)
    have hPγ : P γ := by
      refine (hP γ).2 ⟨hγA, fun y y' hyy' hy'γ hy hy' => ?_⟩
      obtain ⟨h1, h2⟩ := hεlt y y' (hYA hy) (hYA hy')
      have hεγ : ε y y' < γ :=
        (hz _ ⟨(⟨y, hy⟩, ⟨y', hy'⟩), rfl⟩).trans ((le_max_right _ _).trans_lt hγ)
      exact mono y y' (ε y y') γ h1 h2 hεγ hyy'.ne (hεc y y' h1 h2 (hYA hy) (hYA hy'))
    exact (hc γ hPγ).not_gt ((le_max_left _ _).trans_lt hγ)
  have : Nonempty (Kappa κ) :=
    ⟨Kappa.mk 0 (Cardinal.ord_pos.2 (Cardinal.aleph0_pos.trans_le hκ0))⟩
  obtain ⟨y₁, hy₁, -⟩ := hYunb (Classical.arbitrary _)
  have hYne : Y.Nonempty := ⟨y₁, hy₁⟩
  set y₀ := WellFounded.min wellFounded_lt Y hYne
  have hy₀ : y₀ ∈ Y := WellFounded.min_mem _ _ _
  -- the elements of `Y` above `y₀`, and pigeonhole on `C(y₀, ·)`
  set s : Set (Kappa κ) := {y | y ∈ Y ∧ y₀ < y}
  have hsκ : #s = κ := Kappa.card_eq_of_forall_exists_gt hκ fun x => by
    obtain ⟨y, hy, hxy⟩ := hYunb (max x y₀)
    exact ⟨y, ⟨hy, (le_max_right _ _).trans_lt hxy⟩, (le_max_left _ _).trans_lt hxy⟩
  obtain ⟨t, B, hBs, hBκ, hBt⟩ := Cardinal.infinite_pigeonhole_set (s := s)
    (fun y : s => C.color y₀ y y.2.2) κ (by rw [hsκ]) hκ0
    (by rw [Kappa.mk_eq, hκ.cof_ord]; exact hμ)
  refine ⟨B, le_antisymm ((Cardinal.mk_set_le B).trans (Kappa.mk_eq κ).le) hBκ, ?_⟩
  have key : ∀ p : Pairs (Kappa κ), (∀ x ∈ p.1, x ∈ B) → C p = t := by
    intro p hp
    obtain ⟨x, y, hxy, rfl⟩ := p.exists_eq_mk
    have hx := hp x (Sym2.mem_mk_left x y)
    have hy := hp y (Sym2.mem_mk_right x y)
    have hPy := ((hP y).1 (hBs hy).1).2 y₀ x (hBs hx).2 hxy hy₀ (hBs hx).1
    change C.color x y hxy = t
    rw [← hPy]
    exact hBt hy
  exact fun p q hp hq => (key p hp).trans (key q hq).symm
end JardenShami
