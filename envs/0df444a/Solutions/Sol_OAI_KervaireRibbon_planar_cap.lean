-- Prove2me | solution 1 for OAI.KervaireRibbon.planar_cap
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:56:28.058671+00:00
-- url     : https://prove2.me/submissions/844f5be6-05c2-4d3b-84cd-fcb809d39f72

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceDegree
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentExistence
import Definitions.Def_OAI_GroupTheory_Kervaire_SignedIncidence
import Definitions.Def_OAI_GroupTheory_Kervaire_FixedSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_Traversal
import Definitions.Def_OAI_GroupTheory_Kervaire_BoundaryFlow
import Definitions.Def_OAI_GroupTheory_Kervaire_RelatorRigidity

open OAI OAI.KervaireRibbon
open Equiv Equiv.Perm
open scoped Classical
variable {D A : Type*} [Fintype D] [DecidableEq D] [Group A]
theorem kr_swap_rel (r : Setoid D) {p q : D} (h : r p q) (e : D) : r (swap p q e) e :=
  cycle_swap_le r p q h (SameCycle.rfl.apply_left : (swap p q).SameCycle (swap p q e) e)

theorem kr_step_rel (π : Perm D) (r : Setoid D) (h : SameCycle.setoid π ≤ r) (e : D) : r (π e) e :=
  h (SameCycle.rfl.apply_left : π.SameCycle (π e) e)

theorem kr_isolated (π : Perm D) {z : D} (hz : π z = z) :
    SameCycle.setoid π ≤ Setoid.ker (fun d => d = z) := by
  apply cycle_le_of_step
  intro d
  show (π d = z) = (d = z)
  exact propext ⟨fun h => π.injective (h.trans hz.symm), fun h => h ▸ hz⟩

theorem kr_numCycles_erase (π : Perm D) {x : D} (h : π x ≠ x) :
    numCycles (swap x (π x) * π) = numCycles π + 1 :=
  numCycles_swap_split π (fun e => h e.symm) SameCycle.rfl.apply_right

theorem kr_planar_suppress (τ θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hsx : τ x = y) (hsy : τ y = x)
    (hx : θ x ≠ x) (hy : θ y ≠ y) (hp : planar τ θ) :
    planar (swap x y * τ) (suppress θ x y) := by
  unfold planar at hp ⊢
  set σ' := swap x y * τ with hσ'
  set θ' := suppress θ x y with hθ'
  set C := components τ θ with hCdef
  set R := components σ' θ' with hRdef
  have hCτ : ∀ e, C (τ e) e := kr_step_rel τ C le_sup_left
  have hCθ : ∀ e, C (θ e) e := kr_step_rel θ C le_sup_right
  have hRσ : ∀ e, R (σ' e) e := kr_step_rel σ' R le_sup_left
  have hRθ : ∀ e, R (θ' e) e := kr_step_rel θ' R le_sup_right
  have hCxy : C x y := C.symm' (by have := hCτ x; rwa [hsx] at this)
  have hCxa : C x (θ x) := C.symm' (hCθ x)
  have hσ'x : σ' x = x := by simp [hσ', hsx]
  have hσ'y : σ' y = y := by simp [hσ', hsy]
  have hτσ : ∀ e, τ e = swap x y (σ' e) := by intro e; simp [hσ']
  have hθ's : ∀ e, θ' e = swap x y (swap y (θ x) (θ (swap y (θ x) e))) := fun e => rfl
  have hxa : x ≠ θ x := fun h => hx h.symm
  have hθ'x : θ' x = x := by
    rw [hθ's, swap_apply_of_ne_of_ne hxy hxa, swap_apply_right, swap_apply_right]
  have hθ'y : θ' y = y := by
    rw [hθ's, swap_apply_left, hθ, swap_apply_of_ne_of_ne hxy hxa, swap_apply_left]
  have hRx : R ≤ Setoid.ker (fun d => d = x) := sup_le (kr_isolated σ' hσ'x) (kr_isolated θ' hθ'x)
  have hRy : R ≤ Setoid.ker (fun d => d = y) := sup_le (kr_isolated σ' hσ'y) (kr_isolated θ' hθ'y)
  have hnσ : numCycles σ' = numCycles τ + 1 := by
    have := kr_numCycles_erase τ (x := x) (by rw [hsx]; exact Ne.symm hxy)
    rw [hsx] at this; exact this
  by_cases ha : θ x = y
  · -- loop case
    have hθ'e : θ' = swap x y * θ := by
      ext e; rw [hθ's, ha, swap_self]; simp
    have hθy : θ y = x := by rw [← ha, hθ]
    have hnθ : numCycles θ' = numCycles θ + 1 := by
      have := kr_numCycles_erase θ (x := x) hx
      rw [ha] at this; rw [hθ'e]; exact this
    have hφ : σ' * θ' = τ * θ := by
      ext e
      rw [hθ'e]
      simp only [Perm.mul_apply, hσ']
      by_cases h1 : e = x
      · rw [h1, ha, swap_apply_right, hsx, swap_apply_right, hsy]
      by_cases h2 : e = y
      · rw [h2, hθy, swap_apply_left, hsy, swap_apply_left, hsx]
      have h3 : θ e ≠ x := fun h => h2 (by have := congrArg θ h; rw [hθ, ha] at this; exact this)
      have h4 : θ e ≠ y := fun h => h1 (by have := congrArg θ h; rw [hθ, hθy] at this; exact this)
      have h5 : τ (θ e) ≠ x := fun h => h4 (τ.injective (h.trans hsy.symm))
      have h6 : τ (θ e) ≠ y := fun h => h3 (τ.injective (h.trans hsx.symm))
      rw [swap_apply_of_ne_of_ne h3 h4, swap_apply_of_ne_of_ne h5 h6]
    have hJ : joinPair R x y = C := by
      apply le_antisymm
      · apply sup_le (sup_le ?_ ?_) (cycle_swap_le C x y hCxy)
        · apply cycle_le_of_step; intro e
          show C (σ' e) e
          have : σ' e = swap x y (τ e) := by simp [hσ']
          rw [this]; exact C.trans' (kr_swap_rel C hCxy _) (hCτ e)
        · apply cycle_le_of_step; intro e
          show C (θ' e) e
          rw [hθ'e, Perm.mul_apply]; exact C.trans' (kr_swap_rel C hCxy _) (hCθ e)
      · have hJxy := joinPair_rel R x y
        have hRJ : ∀ a b, R a b → joinPair R x y a b := fun a b h => le_joinPair R x y h
        apply sup_le
        · apply cycle_le_of_step; intro e
          show joinPair R x y (τ e) e
          rw [hτσ]; exact (joinPair R x y).trans' (kr_swap_rel _ hJxy _) (hRJ _ _ (hRσ e))
        · apply cycle_le_of_step; intro e
          show joinPair R x y (θ e) e
          have : θ e = swap x y (θ' e) := by rw [hθ'e]; simp
          rw [this]; exact (joinPair R x y).trans' (kr_swap_rel _ hJxy _) (hRJ _ _ (hRθ e))
    have hnR : ¬ R x y := by
      intro h
      have h' : ((x = x) = (y = x)) := hRx h
      exact hxy (by rw [← h'] : y = x).symm
    have hcl := classes_joinPair R hnR
    rw [hJ] at hcl
    rw [hφ]
    omega
  · -- generic case
    set a := θ x with ha'
    set b := θ y with hb'
    have hθa : θ a = x := hθ x
    have hθb : θ b = y := hθ y
    have hay : a ≠ y := ha
    have hbx : b ≠ x := fun h => ha (by have := congrArg θ h; rw [hθ] at this; exact this.symm)
    have hab : a ≠ b := fun h => hxy (θ.injective h)
    have hby : b ≠ y := hy
    let θ'' := swap y a * θ * swap y a
    have hθ'' : θ' = swap x y * θ'' := rfl
    have hn'' : numCycles θ'' = numCycles θ := by
      have := numCycles_conj θ (swap y a)
      rwa [swap_inv] at this
    have h''x : θ'' x = y := by
      simp only [θ'', Perm.mul_apply]
      rw [swap_apply_of_ne_of_ne hxy hxa]; exact swap_apply_right _ _
    have hnθ : numCycles θ' = numCycles θ + 1 := by
      rw [hθ'', ← hn'']
      have := kr_numCycles_erase θ'' (x := x) (by rw [h''x]; exact Ne.symm hxy)
      rw [h''x] at this; exact this
    -- faces
    have hθ'a : θ' a = b := by
      rw [hθ's, swap_apply_right, swap_apply_of_ne_of_ne hby (Ne.symm hab),
        swap_apply_of_ne_of_ne hbx hby]
    have hθ'b : θ' b = a := by
      rw [hθ's, swap_apply_of_ne_of_ne hby (Ne.symm hab), hθb, swap_apply_left,
        swap_apply_of_ne_of_ne (Ne.symm hxa) hay]
    have hθ'o : ∀ e, e ≠ x → e ≠ y → e ≠ a → e ≠ b → θ' e = θ e := by
      intro e h1 h2 h3 h4
      have g1 : θ e ≠ x := fun h => h3 (by have := congrArg θ h; rw [hθ] at this; exact this)
      have g2 : θ e ≠ y := fun h => h4 (by have := congrArg θ h; rw [hθ] at this; exact this)
      have g3 : θ e ≠ a := fun h => h1 (by have := congrArg θ h; rw [hθ, hθa] at this; exact this)
      rw [hθ's, swap_apply_of_ne_of_ne h2 h3, swap_apply_of_ne_of_ne g2 g3,
        swap_apply_of_ne_of_ne g1 g2]
    have hτa : τ a ≠ x := fun h => hay (τ.injective (h.trans hsy.symm))
    have hτa' : τ a ≠ y := fun h => hxa (τ.injective (hsx.trans h.symm))
    have hτb : τ b ≠ x := fun h => hby (τ.injective (h.trans hsy.symm))
    have hτb' : τ b ≠ y := fun h => hbx (τ.injective (h.trans hsx.symm))
    have hτab : τ a ≠ τ b := fun h => hab (τ.injective h)
    have hσ'o : ∀ e, e ≠ x → e ≠ y → σ' e = τ e := by
      intro e h1 h2
      have g1 : τ e ≠ x := fun h => h2 (τ.injective (h.trans hsy.symm))
      have g2 : τ e ≠ y := fun h => h1 (τ.injective (h.trans hsx.symm))
      simp only [hσ', Perm.mul_apply]; exact swap_apply_of_ne_of_ne g1 g2
    have hφ : σ' * θ' = swap y (τ b) * (swap x (τ a) * (τ * θ)) := by
      ext e
      simp only [Perm.mul_apply]
      by_cases h1 : e = x
      · rw [h1, hθ'x, hσ'x, show θ x = a from rfl, swap_apply_right, swap_apply_of_ne_of_ne hxy (Ne.symm hτb)]
      by_cases h2 : e = y
      · rw [h2, hθ'y, hσ'y, show θ y = b from rfl, swap_apply_of_ne_of_ne hτb (Ne.symm hτab), swap_apply_right]
      by_cases h3 : e = a
      · rw [h3, hθ'a, hσ'o b hbx hby, hθa, hsx, swap_apply_of_ne_of_ne (Ne.symm hxy) (Ne.symm hτa'),
          swap_apply_left]
      by_cases h4 : e = b
      · rw [h4, hθ'b, hσ'o a (Ne.symm hxa) hay, hθb, hsy, swap_apply_left,
          swap_apply_of_ne_of_ne hτa' hτab]
      rw [hθ'o e h1 h2 h3 h4]
      have g1 : θ e ≠ x := fun h => h3 (by have := congrArg θ h; rw [hθ] at this; exact this)
      have g2 : θ e ≠ y := fun h => h4 (by have := congrArg θ h; rw [hθ] at this; exact this)
      have g3 : θ e ≠ a := fun h => h1 (by have := congrArg θ h; rw [hθ, hθa] at this; exact this)
      have g4 : θ e ≠ b := fun h => h2 (by have := congrArg θ h; rw [hθ, hθb] at this; exact this)
      rw [hσ'o _ g1 g2]
      have k1 : τ (θ e) ≠ x := fun h => g2 (τ.injective (h.trans hsy.symm))
      have k2 : τ (θ e) ≠ y := fun h => g1 (τ.injective (h.trans hsx.symm))
      have k3 : τ (θ e) ≠ τ a := fun h => g3 (τ.injective h)
      have k4 : τ (θ e) ≠ τ b := fun h => g4 (τ.injective h)
      rw [swap_apply_of_ne_of_ne k1 k3, swap_apply_of_ne_of_ne k2 k4]
    have hnφ : numCycles (σ' * θ') = numCycles (τ * θ) + 2 := by
      have e1 := kr_numCycles_erase (τ * θ) (x := x) (by
        simp only [Perm.mul_apply, ← ha']; exact hτa)
      have hφ1 : (swap x ((τ * θ) x) * (τ * θ)) y = τ b := by
        simp only [Perm.mul_apply, ← ha', ← hb']; exact swap_apply_of_ne_of_ne hτb (Ne.symm hτab)
      have e2 := kr_numCycles_erase (swap x ((τ * θ) x) * (τ * θ)) (x := y) (by rw [hφ1]; exact hτb')
      rw [hφ1] at e2
      have hx' : (τ * θ) x = τ a := by simp [← ha']
      rw [hφ, ← hx', e2, e1]
    -- components
    set J1 := joinPair R x a with hJ1
    set J := joinPair J1 y a with hJdef
    have hCya : C y a := C.trans' (C.symm' hCxy) hCxa
    have hJ : J = C := by
      apply le_antisymm
      · apply sup_le (sup_le (sup_le ?_ ?_) (cycle_swap_le C x a hCxa)) (cycle_swap_le C y a hCya)
        · apply cycle_le_of_step; intro e
          show C (σ' e) e
          have : σ' e = swap x y (τ e) := by simp [hσ']
          rw [this]; exact C.trans' (kr_swap_rel C hCxy _) (hCτ e)
        · apply cycle_le_of_step; intro e
          show C (θ' e) e
          rw [hθ's]
          exact C.trans' (kr_swap_rel C hCxy _) (C.trans' (kr_swap_rel C hCya _)
            (C.trans' (hCθ _) (kr_swap_rel C hCya _)))
      · have hJxa : J x a := le_joinPair J1 y a (joinPair_rel R x a)
        have hJya : J y a := joinPair_rel J1 y a
        have hJxy : J x y := J.trans' hJxa (J.symm' hJya)
        have hRJ : ∀ p q, R p q → J p q := fun p q h => le_joinPair J1 y a (le_joinPair R x a h)
        apply sup_le
        · apply cycle_le_of_step; intro e
          show J (τ e) e
          rw [hτσ]; exact J.trans' (kr_swap_rel _ hJxy _) (hRJ _ _ (hRσ e))
        · apply cycle_le_of_step; intro e
          show J (θ e) e
          have : θ e = swap y a (swap x y (θ' (swap y a e))) := by
            rw [hθ's]; simp [swap_apply_self]
          rw [this]
          exact J.trans' (kr_swap_rel J hJya _) (J.trans' (kr_swap_rel J hJxy _)
            (J.trans' (hRJ _ _ (hRθ _)) (kr_swap_rel J hJya _)))
    have hnR : ¬ R x a := by
      intro h
      have h' : ((x = x) = (a = x)) := hRx h
      exact hxa (by rw [← h'] : a = x).symm
    have hnJ1 : ¬ J1 y a := by
      have hle : J1 ≤ Setoid.ker (fun d => d = y) := by
        apply sup_le hRy
        apply cycle_le_of_step; intro e
        show (swap x a e = y) = (e = y)
        apply propext
        rw [swap_apply_eq_iff, swap_apply_of_ne_of_ne (Ne.symm hxy) (Ne.symm hay)]
      intro h
      have h' : ((y = y) = (a = y)) := hle h
      exact hay (by rw [← h'])
    have hc1 := classes_joinPair R hnR
    have hc2 := classes_joinPair J1 hnJ1
    rw [← hJ1] at hc1
    rw [← hJdef, hJ] at hc2
    omega

theorem solution (σ θ : Perm D) (hθ : ∀ d, θ (θ d) = d)
    {x y : D} (hxy : x ≠ y) (hs : σ x = y) (hz : σ y ≠ x)
    (hx : θ x ≠ x) (hy : θ y ≠ y) (hp : planar σ θ) :
    planar (erase (erase σ x) y) (suppress θ x y) := by
  have hyy : σ y ≠ y := fun h => hxy (σ.injective (by rw [hs, h]))
  have hcv : erase (erase σ x) y = swap x y * (swap x (σ y) * σ) := by
    have h1 : erase σ x = swap x y * σ := by simp [erase, hs]
    have h2 : (swap x y * σ) y = σ y := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hz hyy]
    rw [h1, erase, h2]
    ext d
    simp only [Perm.mul_apply]
    generalize σ d = e
    generalize hc : σ y = c at hz hyy
    by_cases e1 : e = x
    · subst e1; rw [swap_apply_left, swap_apply_left, swap_apply_left, swap_apply_of_ne_of_ne hz hyy]
    by_cases e2 : e = y
    · subst e2; rw [swap_apply_right, swap_apply_of_ne_of_ne hxy (Ne.symm hz), swap_apply_of_ne_of_ne (Ne.symm hxy) (Ne.symm hyy), swap_apply_right]
    by_cases e3 : e = c
    · subst e3; rw [swap_apply_of_ne_of_ne hz hyy, swap_apply_right, swap_apply_right, swap_apply_left]
    rw [swap_apply_of_ne_of_ne e1 e2, swap_apply_of_ne_of_ne e2 e3, swap_apply_of_ne_of_ne e1 e3, swap_apply_of_ne_of_ne e1 e2]
  rw [hcv]
  have hxc : x ≠ σ y := Ne.symm hz
  have hsame : σ.SameCycle x (σ y) := ⟨2, by rw [zpow_two, Perm.mul_apply, hs]⟩
  have hp1 := planar_vertex_split σ θ hxc hsame hp
  have hyc : y ≠ σ y := Ne.symm hyy
  apply kr_planar_suppress _ θ hθ hxy _ _ hx hy hp1
  · rw [Perm.mul_apply, hs, swap_apply_of_ne_of_ne (Ne.symm hxy) hyc]
  · rw [Perm.mul_apply, swap_apply_right]

