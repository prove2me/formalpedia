-- Prove2me | solution 1 for Ideal.exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/50175428-7101-52ed-91ea-0fe65837f10c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg

set_option autoImplicit false

namespace ClosedSpread

theorem exists_not_mem_mul_le_of_map_le {S B Bp : Type} [CommRing S] [CommRing B] [CommRing Bp]
    (φ : S →+* B) (𝔭 : Ideal S) [𝔭.IsPrime] (J₁ J₂ : Ideal B) (h₁ : J₁.FG)
    [Algebra B Bp] [IsLocalization (𝔭.primeCompl.map φ.toMonoidHom) Bp]
    (h : J₁.map (algebraMap B Bp) ≤ J₂.map (algebraMap B Bp)) :
    ∃ s : S, s ∉ 𝔭 ∧ ∀ x ∈ J₁, φ s * x ∈ J₂ := by
  classical
  obtain ⟨gens, hgens⟩ := h₁

  have key : ∀ x ∈ J₁, ∃ s : S, s ∉ 𝔭 ∧ φ s * x ∈ J₂ := by
    intro x hx
    have hx' : algebraMap B Bp x ∈ J₂.map (algebraMap B Bp) := h (Ideal.mem_map_of_mem _ hx)
    obtain ⟨⟨a, t⟩, hat⟩ := (IsLocalization.mem_map_algebraMap_iff (𝔭.primeCompl.map φ.toMonoidHom) Bp).mp hx'

    have hat' : algebraMap B Bp (x * (t : B)) = algebraMap B Bp (a : B) := by
      rw [map_mul]; exact hat
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (𝔭.primeCompl.map φ.toMonoidHom) Bp).mp hat'

    obtain ⟨sc, hsc, hscq⟩ := Submonoid.mem_map.mp c.2
    obtain ⟨st, hst, hstq⟩ := Submonoid.mem_map.mp t.2
    refine ⟨sc * st, ?_, ?_⟩
    · intro hmem
      rcases (Ideal.IsPrime.mem_or_mem ‹𝔭.IsPrime› hmem) with h' | h'
      · exact hsc h'
      · exact hst h'
    · have : φ (sc * st) * x = (c : B) * (x * (t : B)) := by
        rw [map_mul, show φ sc = (c : B) from hscq, show φ st = ((t : _) : B) from hstq]; ring
      rw [this, hc]
      exact J₂.mul_mem_left _ a.2
  choose sf hsf using key
  refine ⟨∏ x ∈ gens.attach, sf x.1 (hgens ▸ Ideal.subset_span x.2), ?_, ?_⟩
  · refine Finset.prod_induction _ (fun y : S => y ∉ 𝔭) ?_ ?_ ?_
    · intro a b ha hb hab
      rcases (Ideal.IsPrime.mem_or_mem ‹𝔭.IsPrime› hab) with h' | h'
      · exact ha h'
      · exact hb h'
    · exact (Ideal.ne_top_iff_one 𝔭).mp (Ideal.IsPrime.ne_top ‹_›)
    · intro x _
      exact (hsf x.1 _).1
  · intro x hx
    rw [← hgens] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      obtain ⟨rest, hrest⟩ : ∃ rest : S, (∏ x ∈ gens.attach, sf x.1 (hgens ▸ Ideal.subset_span x.2)) =
          sf y (hgens ▸ Ideal.subset_span hy) * rest := by
        refine ⟨∏ x ∈ (gens.attach.erase ⟨y, hy⟩), sf x.1 (hgens ▸ Ideal.subset_span x.2), ?_⟩
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_attach _ ⟨y, hy⟩)]
      rw [hrest, map_mul, mul_comm (φ _) (φ rest), mul_assoc]
      exact J₂.mul_mem_left _ (hsf y _).2
    · simp
    · intro y z _ _ hy hz
      rw [mul_add]; exact J₂.add_mem hy hz
    · intro r y _ hy
      rw [smul_eq_mul, mul_left_comm]
      exact J₂.mul_mem_left _ hy

theorem exists_not_mem_map_eq_map {S B Bp : Type} [CommRing S] [CommRing B] [CommRing Bp]
    (φ : S →+* B) (𝔭 : Ideal S) [𝔭.IsPrime] (J₁ J₂ : Ideal B) (h₁ : J₁.FG) (h₂ : J₂.FG)
    [Algebra B Bp] [IsLocalization (𝔭.primeCompl.map φ.toMonoidHom) Bp]
    (h : J₁.map (algebraMap B Bp) = J₂.map (algebraMap B Bp)) :
    ∃ g : S, g ∉ 𝔭 ∧ ∀ (Bg : Type) [CommRing Bg] [Algebra B Bg]
      [IsLocalization (Submonoid.powers (φ g)) Bg],
      J₁.map (algebraMap B Bg) = J₂.map (algebraMap B Bg) := by
  obtain ⟨s₁, hs₁, H₁⟩ := exists_not_mem_mul_le_of_map_le φ 𝔭 J₁ J₂ h₁ h.le
  obtain ⟨s₂, hs₂, H₂⟩ := exists_not_mem_mul_le_of_map_le φ 𝔭 J₂ J₁ h₂ h.ge
  refine ⟨s₁ * s₂, ?_, ?_⟩
  · intro hmem
    rcases (Ideal.IsPrime.mem_or_mem ‹𝔭.IsPrime› hmem) with h' | h'
    · exact hs₁ h'
    · exact hs₂ h'
  intro Bg _ _ _
  have hunit : IsUnit (algebraMap B Bg (φ (s₁ * s₂))) :=
    IsLocalization.map_units Bg (⟨φ (s₁ * s₂), Submonoid.mem_powers _⟩ : Submonoid.powers (φ (s₁ * s₂)))
  have hu₁ : IsUnit (algebraMap B Bg (φ s₁)) := by
    rw [map_mul, map_mul] at hunit; exact isUnit_of_mul_isUnit_left hunit
  have hu₂ : IsUnit (algebraMap B Bg (φ s₂)) := by
    rw [map_mul, map_mul] at hunit; exact isUnit_of_mul_isUnit_right hunit
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    have : algebraMap B Bg x = hu₁.unit⁻¹ * algebraMap B Bg (φ s₁ * x) := by
      rw [map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (H₁ x hx))
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    have : algebraMap B Bg x = hu₂.unit⁻¹ * algebraMap B Bg (φ s₂ * x) := by
      rw [map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (H₂ x hx))

end ClosedSpread

theorem solution
    {S B : Type} [CommRing S] [CommRing B] (φ : S →+* B) (𝔭 : Ideal S) [𝔭.IsPrime]
    (Bₚ : Type) [CommRing Bₚ] [Algebra B Bₚ] [IsLocalization (𝔭.primeCompl.map φ.toMonoidHom) Bₚ]
    (J₁ J₂ : Ideal B) (h₁ : J₁.FG) (h₂ : J₂.FG)
    (h : J₁.map (algebraMap B Bₚ) = J₂.map (algebraMap B Bₚ)) :
    ∃ g : S, g ∉ 𝔭 ∧
      ∀ (B' : Type) [CommRing B'] [Algebra B B'] [IsLocalization.Away (φ g) B'],
        J₁.map (algebraMap B B') = J₂.map (algebraMap B B') := by
  exact ClosedSpread.exists_not_mem_map_eq_map φ 𝔭 J₁ J₂ h₁ h₂ (Bp := Bₚ) h

end S_Ideal_exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg
end P2MW
export P2MW.S_Ideal_exists_not_mem_forall_map_eq_map_of_isLocalization_of_map_eq_map_of_fg (solution)
