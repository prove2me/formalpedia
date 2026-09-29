-- Prove2me | solution 1 for MvFormalGroup.CartierModule.exists_tangent_eq_and_coeff_subst_eq_ghost_of_log
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/974c005b-eaef-5b39-a982-a8de919abd56

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Theorems.Thm_MvFormalGroup_WittLaw_subst_addFam_eq_add_of_coeff_eq_ghost
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_CartierModule_exists_tangent_eq_and_coeff_subst_eq_ghost_of_log

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open MvPowerSeries

noncomputable section

namespace GHEBody

open Classical

variable (p : ℕ) [hp : Fact p.Prime] {𝓞 : Type u} [CommRing 𝓞]

theorem single_pow_inj {k n k' n' : ℕ}
    (h : (Finsupp.single k (p ^ n) : ℕ →₀ ℕ) = Finsupp.single k' (p ^ n')) : k = k' ∧ n = n' := by
  rcases (Finsupp.single_eq_single_iff _ _ _ _).mp h with ⟨hk, hpn⟩ | ⟨h0, -⟩
  · exact ⟨hk, Nat.pow_right_injective hp.out.two_le hpn⟩
  · exact absurd h0 (pow_ne_zero _ hp.out.ne_zero)

def ghostS (c : ℕ → 𝓞) : MvPowerSeries ℕ 𝓞 := fun e =>
  if h : ∃ kn : ℕ × ℕ, e = Finsupp.single kn.1 (p ^ kn.2)
  then (p : 𝓞) ^ h.choose.1 * c (h.choose.1 + h.choose.2) else 0

theorem coeff_ghostS_single (c : ℕ → 𝓞) (k n : ℕ) :
    coeff (Finsupp.single k (p ^ n)) (ghostS p c) = (p : 𝓞) ^ k * c (k + n) := by
  show ghostS p c (Finsupp.single k (p ^ n)) = _
  unfold ghostS
  have hex : ∃ kn : ℕ × ℕ, (Finsupp.single k (p ^ n) : ℕ →₀ ℕ) = Finsupp.single kn.1 (p ^ kn.2) :=
    ⟨(k, n), rfl⟩
  rw [dif_pos hex]
  obtain ⟨hk, hn⟩ := single_pow_inj p hex.choose_spec
  rw [← hk, ← hn]

theorem coeff_ghostS_of_ne (c : ℕ → 𝓞) (e : ℕ →₀ ℕ)
    (he : ∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) : coeff e (ghostS p c) = 0 := by
  show ghostS p c e = _
  unfold ghostS
  rw [dif_neg]
  rintro ⟨⟨k, n⟩, hkn⟩
  exact he k n hkn

theorem coeff_ghostS_single_zero_one (c : ℕ → 𝓞) :
    coeff (Finsupp.single 0 1) (ghostS p c) = c 0 := by
  have := coeff_ghostS_single p c 0 0
  rwa [pow_zero, pow_zero, one_mul, zero_add] at this

theorem constantCoeff_ghostS (c : ℕ → 𝓞) : constantCoeff (ghostS p c) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  refine coeff_ghostS_of_ne p c 0 fun k n h => ?_
  have := congrArg (fun e : ℕ →₀ ℕ => e k) h
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_eq_same] at this
  exact absurd this.symm (pow_ne_zero _ hp.out.ne_zero)

variable {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm]
  (f ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
  (hf0 : ∀ i, (f i).constantCoeff = 0)
  (hf1 : ∀ i j : Fin d, (coeff (Finsupp.single j 1) (f i) : 𝓞) = if i = j then 1 else 0)
  (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
  (hfψ : ∀ i, subst ψ (f i) = X i) (hψf : ∀ i, subst f (ψ i) = X i)
  (hlog : ∀ i, subst Φ.toPowerSeries (f i) =
    subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (f i) +
      subst (fun j => X (Sum.inr j)) (f i))
  (c : ℕ → Fin d → 𝓞)

def G (c : ℕ → Fin d → 𝓞) : Fin d → MvPowerSeries ℕ 𝓞 := fun j => ghostS p (fun N => c N j)

theorem constantCoeff_G (j : Fin d) : (G p c j).constantCoeff = 0 := constantCoeff_ghostS p _

theorem hasSubst_G : HasSubst (G p c) := hasSubst_of_constantCoeff_zero (constantCoeff_G p c)

theorem subst_addFam_G (j : Fin d) :
    subst (MvFormalGroup.WittLaw.addFam p 𝓞) (G p c j) =
      subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)) (G p c j) +
        subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)) (G p c j) :=
  MvFormalGroup.WittLaw.subst_addFam_eq_add_of_coeff_eq_ghost p (fun N => c N j) (G p c j)
    (coeff_ghostS_single p _) (coeff_ghostS_of_ne p _)

def mser (ψ : Fin d → MvPowerSeries (Fin d) 𝓞) (c : ℕ → Fin d → 𝓞) : Fin d → MvPowerSeries ℕ 𝓞 :=
  fun j => subst (G p c) (ψ j)

include hψ0 in
theorem constantCoeff_mser (j : Fin d) : (mser p ψ c j).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_G p c) (constantCoeff_G p c) (hψ0 j)

include hψ0 in
theorem hasSubst_mser : HasSubst (mser p ψ c) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_mser p ψ hψ0 c)

include hψ0 hfψ in

theorem subst_mser_f (j : Fin d) : subst (mser p ψ c) (f j) = G p c j := by
  have hψ : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  show subst (fun i => subst (G p c) (ψ i)) (f j) = G p c j
  rw [← subst_comp_subst_apply hψ (hasSubst_G p c), hfψ j, subst_X (hasSubst_G p c)]

include hf0 hψf hlog in

theorem law_eq (j : Fin d) :
    Φ.toPowerSeries j = subst (fun i =>
      subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (f i) +
        subst (fun l => X (Sum.inr l)) (f i)) (ψ j) := by
  have hf : HasSubst f := hasSubst_of_constantCoeff_zero hf0
  have := congrArg (subst Φ.toPowerSeries) (hψf j)
  rw [subst_X Φ.hasSubst_toPowerSeries, subst_comp_subst_apply hf Φ.hasSubst_toPowerSeries] at this
  rw [← this]
  congr 1
  funext i
  exact hlog i

theorem subst_addLog {τ : Type*} (e : Fin d ⊕ Fin d → MvPowerSeries τ 𝓞)
    (he : ∀ s, (e s).constantCoeff = 0) (i : Fin d) :
    subst e (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (f i) +
        subst (fun l => X (Sum.inr l)) (f i)) =
      subst (fun l => e (Sum.inl l)) (f i) + subst (fun l => e (Sum.inr l)) (f i) := by
  have hes : HasSubst e := hasSubst_of_constantCoeff_zero he
  have hinl : HasSubst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hinr : HasSubst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  rw [subst_add hes, subst_comp_subst_apply hinl hes, subst_comp_subst_apply hinr hes]
  simp only [subst_X hes]

include hf0 hψ0 hfψ hψf hlog in

theorem mser_subst_eq (j : Fin d) :
    subst (MvFormalGroup.WittLaw.addFam p 𝓞) (mser p ψ c j) =
      subst
        (Sum.elim
          (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)) (mser p ψ c l))
          fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)) (mser p ψ c l))
        (Φ.toPowerSeries j) := by
  have hψ : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  have hA := MvFormalGroup.WittLaw.hasSubst_addFam p 𝓞
  have hm0 := constantCoeff_mser p ψ hψ0 c
  have hb0 : ∀ m : ℕ, ((X (0, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)).constantCoeff = 0 :=
    fun _ => constantCoeff_X _
  have hb1 : ∀ m : ℕ, ((X (1, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)).constantCoeff = 0 :=
    fun _ => constantCoeff_X _
  have hB0 : HasSubst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)) :=
    MvFormalGroup.WittLaw.hasSubst_blk (R := 𝓞) 0
  have hB1 : HasSubst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)) :=
    MvFormalGroup.WittLaw.hasSubst_blk (R := 𝓞) 1

  set E : Fin d ⊕ Fin d → MvPowerSeries (Fin 2 × ℕ) 𝓞 := Sum.elim
      (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)) (mser p ψ c l))
      fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)) (mser p ψ c l) with hE
  have hE0 : ∀ s, (E s).constantCoeff = 0 := by
    rintro (l | l)
    · exact constantCoeff_subst_eq_zero hB0 hb0 (hm0 l)
    · exact constantCoeff_subst_eq_zero hB1 hb1 (hm0 l)
  have hEs : HasSubst E := hasSubst_of_constantCoeff_zero hE0

  have lhs : subst (MvFormalGroup.WittLaw.addFam p 𝓞) (mser p ψ c j) =
      subst (fun i => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)) (G p c i) +
        subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)) (G p c i)) (ψ j) := by
    show subst (MvFormalGroup.WittLaw.addFam p 𝓞) (subst (G p c) (ψ j)) = _
    rw [subst_comp_subst_apply (hasSubst_G p c) hA]
    congr 1
    funext i
    exact subst_addFam_G p c i

  have rhs : subst E (Φ.toPowerSeries j) =
      subst (fun i => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)) (G p c i) +
        subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)) (G p c i)) (ψ j) := by
    have hinl : HasSubst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have hinr : HasSubst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
      hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    have hAL : HasSubst (fun i => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (f i) +
        subst (fun l => X (Sum.inr l)) (f i)) := by
      refine hasSubst_of_constantCoeff_zero fun i => ?_
      rw [map_add, constantCoeff_subst_eq_zero hinl (fun _ => constantCoeff_X _) (hf0 i),
        constantCoeff_subst_eq_zero hinr (fun _ => constantCoeff_X _) (hf0 i), add_zero]
    rw [law_eq Φ f ψ hf0 hψf hlog j, subst_comp_subst_apply hAL hEs]
    congr 1
    funext i
    rw [subst_addLog f E hE0 i]
    have h0 : (fun l => E (Sum.inl l)) = fun l =>
        subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)) (mser p ψ c l) := by
      funext l; rw [hE]; rfl
    have h1 : (fun l => E (Sum.inr l)) = fun l =>
        subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) 𝓞)) (mser p ψ c l) := by
      funext l; rw [hE]; rfl
    rw [h0, h1, ← subst_comp_subst_apply (hasSubst_mser p ψ hψ0 c) hB0,
      ← subst_comp_subst_apply (hasSubst_mser p ψ hψ0 c) hB1, subst_mser_f p f ψ hψ0 hfψ c i]
  rw [lhs, rhs]

def mElt (Φ : MvFormalGroup d 𝓞) [Φ.IsComm]
    (f ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hf0 : ∀ i, (f i).constantCoeff = 0)
    (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hfψ : ∀ i, subst ψ (f i) = X i) (hψf : ∀ i, subst f (ψ i) = X i)
    (hlog : ∀ i, subst Φ.toPowerSeries (f i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (f i) +
        subst (fun j => X (Sum.inr j)) (f i))
    (c : ℕ → Fin d → 𝓞) : MvFormalGroup.CartierModule p Φ where
  toPowerSeries := mser p ψ c
  constantCoeff_eq_zero := constantCoeff_mser p ψ hψ0 c
  subst_eq := mser_subst_eq p Φ f ψ hf0 hψ0 hfψ hψf hlog c

include hf0 hf1 hψf in

theorem coeff_single_ψ (j t : Fin d) :
    coeff (Finsupp.single t 1) (ψ j) = if j = t then 1 else 0 := by
  classical
  have := congrArg (coeff (Finsupp.single t 1)) (hψf j)
  rw [MvFormalGroup.coeff_single_subst hf0 (ψ j) t, coeff_X] at this
  simp only [hf1] at this
  rw [Fintype.sum_eq_single t (fun s hs => by rw [if_neg hs, mul_zero])] at this
  simp only [if_true, mul_one] at this
  rw [this]
  by_cases h : j = t
  · subst h; simp
  · rw [if_neg h, if_neg]
    intro hh
    exact h (Finsupp.single_left_injective one_ne_zero hh).symm

end GHEBody

open GHEBody in
theorem solution
    (p : ℕ) [Fact p.Prime] {𝓞 : Type u} [CommRing 𝓞] {d : ℕ}
    (Φ : MvFormalGroup d 𝓞) [Φ.IsComm]
    (f ψ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hf0 : ∀ i, (f i).constantCoeff = 0)
    (hf1 : ∀ i j : Fin d, (coeff (Finsupp.single j 1) (f i) : 𝓞) = if i = j then 1 else 0)
    (hψ0 : ∀ i, (ψ i).constantCoeff = 0)
    (hfψ : ∀ i, subst ψ (f i) = X i) (hψf : ∀ i, subst f (ψ i) = X i)
    (hlog : ∀ i, subst Φ.toPowerSeries (f i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (f i) +
        subst (fun j => X (Sum.inr j)) (f i))
    (c : ℕ → Fin d → 𝓞) :
    ∃ m : MvFormalGroup.CartierModule p Φ,
      (∀ j, MvFormalGroup.CartierModule.tangent m j = c 0 j) ∧
      (∀ (j : Fin d) (k n : ℕ),
        (coeff (Finsupp.single k (p ^ n)) (subst m.toPowerSeries (f j)) : 𝓞) = (p : 𝓞) ^ k * c (k + n) j) ∧
      (∀ (j : Fin d) (e : ℕ →₀ ℕ), (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) →
        (coeff e (subst m.toPowerSeries (f j)) : 𝓞) = 0) := by
  classical
  refine ⟨mElt p Φ f ψ hf0 hψ0 hfψ hψf hlog c, fun j => ?_, fun j k n => ?_, fun j e he => ?_⟩
  ·
    show coeff (Finsupp.single 0 1) (subst (G p c) (ψ j)) = c 0 j
    rw [MvFormalGroup.coeff_single_subst (constantCoeff_G p c) (ψ j) 0]
    simp only [coeff_single_ψ f ψ hf0 hf1 hψf]
    rw [Fintype.sum_eq_single j (fun s hs => by rw [if_neg (Ne.symm hs), zero_mul])]
    rw [if_pos rfl, one_mul]
    exact coeff_ghostS_single_zero_one p _
  · show coeff (Finsupp.single k (p ^ n)) (subst (mser p ψ c) (f j)) = _
    rw [subst_mser_f p f ψ hψ0 hfψ c j]
    exact coeff_ghostS_single p _ k n
  · show coeff e (subst (mser p ψ c) (f j)) = 0
    rw [subst_mser_f p f ψ hψ0 hfψ c j]
    exact coeff_ghostS_of_ne p _ e he

end
end S_MvFormalGroup_CartierModule_exists_tangent_eq_and_coeff_subst_eq_ghost_of_log
end P2MW
export P2MW.S_MvFormalGroup_CartierModule_exists_tangent_eq_and_coeff_subst_eq_ghost_of_log (solution)
