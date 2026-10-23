-- Prove2me | solution 1 for MWT.commutator_perfect
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-23T01:35:04.220988+00:00
-- url     : https://prove2.me/submissions/f0d843b4-40ee-4645-a523-0a9a4b8784bc

import Mathlib
import Definitions.Def_MWT_alg
import Definitions.Def_MWT_tor

open MWT


/-- A degenerate world: every generator is `1`. -/
def mwt84_triv (n k : ℕ) (hk : 0 < k) (G : Type) [Group G] : MultiWeldedTwinWorld n k G Unit where
  s := fun _ => 1
  rho := fun _ _ => 1
  s_sq := fun _ => mul_one 1
  s_comm := fun _ _ _ => rfl
  rho_sq := fun _ _ => mul_one 1
  rho_braid := fun _ _ _ => rfl
  rho_comm := fun _ _ _ _ => rfl
  mixed_comm := fun _ _ _ _ => rfl
  mr2 := fun _ _ _ => rfl
  vcomm := fun _ _ _ _ _ _ => rfl
  vmixed1 := fun _ _ _ _ _ => rfl
  vmixed2 := fun _ _ _ _ _ => rfl
  welded := fun _ _ _ => rfl
  hk := hk
  perm := 1
  uwRho := fun _ => 1
  uwSigma := fun _ _ => 1
  uw := 1
  uwRhoMap := fun _ => rfl
  uwSigmaMap := fun _ t => by split_ifs <;> rfl

theorem mwt84_second {n k : ℕ} {G UW : Type*} [Group G] [Group UW]
    (W : MultiWeldedTwinWorld n k G UW) (α : Fin k) (i : ℕ) (hi : i + 3 ≤ n) :
    W.s ⟨i, by omega⟩ * W.s ⟨i + 1, by omega⟩ * W.rho α ⟨i, by omega⟩
      = W.rho α ⟨i + 1, by omega⟩ * W.s ⟨i, by omega⟩ * W.s ⟨i + 1, by omega⟩ := by
  have h := congrArg (·⁻¹) (W.welded α i hi)
  have inv_s : ∀ j, (W.s j)⁻¹ = W.s j := fun j => inv_eq_of_mul_eq_one_right (W.s_sq j)
  have inv_r : ∀ j, (W.rho α j)⁻¹ = W.rho α j := fun j => inv_eq_of_mul_eq_one_right (W.rho_sq α j)
  simp only [mul_inv_rev, inv_s, inv_r] at h
  simpa [mul_assoc] using h

theorem mwt84_uw {n k : ℕ} {G UW : Type*} [Group G] [Group UW]
    (W : MultiWeldedTwinWorld n k G UW) :
    ∀ (i : Fin (n - 1)) (t : Fin k),
      W.uw (W.uwSigma i t * W.uwSigma i t) = 1 ∧
      W.uw (W.uwRho i * W.uwRho i) = 1 := by
  intro i t
  refine ⟨?_, ?_⟩
  · rw [map_mul, W.uwSigmaMap]
    split_ifs
    · exact W.rho_sq _ _
    · exact W.s_sq _
  · rw [map_mul, W.uwRhoMap]; exact W.rho_sq _ _

theorem mwt84_chain {n : ℕ} {A : Type*} (f : Fin (n - 1) → A)
    (h : ∀ (i : ℕ) (hi : i + 3 ≤ n), f ⟨i, by omega⟩ = f ⟨i + 1, by omega⟩) :
    ∀ i j : Fin (n - 1), f i = f j := by
  have h0 : ∀ i : Fin (n - 1), ∀ (h0 : 0 < n - 1), f i = f ⟨0, h0⟩ := by
    rintro ⟨i, hi⟩ h0
    induction i with
    | zero => rfl
    | succ m ih => rw [← h m (by omega)]; exact ih (by omega)
  intro i j
  have hp : 0 < n - 1 := by have := i.2; omega
  rw [h0 i hp, h0 j hp]

theorem mwt84_collapse {n k : ℕ} {G UW : Type*} [Group G] [Group UW]
    (W : MultiWeldedTwinWorld n k G UW) :
    (∀ i j : Fin (n - 1), Abelianization.of (W.s i) = Abelianization.of (W.s j)) ∧
    (∀ (α : Fin k) (i j : Fin (n - 1)),
      Abelianization.of (W.rho α i) = Abelianization.of (W.rho α j)) := by
  constructor
  · apply mwt84_chain (fun j => Abelianization.of (W.s j))
    intro i hi
    have h := congrArg Abelianization.of (W.mr2 ⟨0, W.hk⟩ i hi)
    simp only [map_mul] at h
    rw [mul_assoc (Abelianization.of (W.s _)), mul_comm (Abelianization.of (W.s _))] at h
    exact mul_left_cancel h
  · intro α
    apply mwt84_chain (fun j => Abelianization.of (W.rho α j))
    intro i hi
    have h := congrArg Abelianization.of (W.rho_braid α i hi)
    simp only [map_mul] at h
    rw [mul_comm (Abelianization.of (W.rho α ⟨i + 1, _⟩)) (Abelianization.of (W.rho α ⟨i, _⟩))] at h
    exact mul_left_cancel h

theorem mwt84_goal {n k : ℕ} {G UW : Type*} [Group G] [Group UW]
    (W : MultiWeldedTwinWorld n k G UW) :
    ∃ (F : Type) (_ : Group F) (_ : Fintype F) (q : G →* F),
      2 ^ k * Nat.factorial n ≤ Fintype.card F := by
  have hpos : 0 < 2 ^ k * Nat.factorial n := by positivity
  have : NeZero (2 ^ k * Nat.factorial n) := ⟨hpos.ne'⟩
  refine ⟨Multiplicative (ZMod (2 ^ k * Nat.factorial n)), inferInstance, inferInstance, 1, ?_⟩
  simp

/-! Disproofs -/

theorem mwt84_abel_false : ¬ Nonempty (Abelianization Unit ≃* Multiplicative (Fin (1 + 1) → ZMod 2)) := by
  rintro ⟨e⟩
  have hs : ∀ x y : Abelianization Unit, x = y := by
    intro x y
    induction x using QuotientGroup.induction_on
    induction y using QuotientGroup.induction_on
    rfl
  have := e.symm.injective (hs (e.symm 1) (e.symm (Multiplicative.ofAdd (fun _ => 1))))
  have := congrFun (congrArg Multiplicative.toAdd this) 0
  simp at this

theorem mwt84_sym_false : ¬ ∀ p : Equiv.Perm (Fin 5), ∃ x : Unit, (mwt84_triv 5 1 one_pos Unit).perm x = p := by
  intro h
  obtain ⟨x, hx⟩ := h (Equiv.swap 0 1)
  have : (Equiv.swap (0 : Fin 5) 1) = 1 := hx.symm
  have h2 := congrArg (fun p : Equiv.Perm (Fin 5) => p 0) this
  simp at h2

theorem mwt84_wit_false : ¬ ∃ (A : Type) (_ : CommGroup A) (_ : Fintype A) (hA : Fintype.card A = 2 ^ (1 + 1))
      (th : Unit →* Equiv.Perm (Fin 2) × A),
      (∀ x : Unit, (th x).1 = (mwt84_triv 2 1 one_pos Unit).perm x) ∧
      (∀ (i : Fin (2 - 1)) (α : Fin 1),
        (th ((mwt84_triv 2 1 one_pos Unit).s i * (mwt84_triv 2 1 one_pos Unit).rho α i)).2 ≠ 1) := by
  rintro ⟨A, _, _, _, th, -, h⟩
  apply h 0 0
  have : (mwt84_triv 2 1 one_pos Unit).s 0 * (mwt84_triv 2 1 one_pos Unit).rho 0 0 = 1 := rfl
  rw [this, map_one]; rfl

/-- In `D₃` every commutator is a rotation. -/
theorem mwt84_d3_comm : ∀ a b : DihedralGroup 3, ∃ i, a * b * a⁻¹ * b⁻¹ = DihedralGroup.r i := by
  decide

theorem mwt84_perfect_false : ¬ DerivedPerfect (DihedralGroup 3) := by
  intro h
  -- the derived subgroup lies in the rotation subgroup, which is commutative
  let R : Subgroup (DihedralGroup 3) := Subgroup.closure (Set.range DihedralGroup.r)
  have hR : ∀ x ∈ R, ∃ i, x = DihedralGroup.r i := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact ⟨i, rfl⟩
    | one => exact ⟨0, rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, rfl⟩ := hx; obtain ⟨j, rfl⟩ := hy; exact ⟨i + j, by simp⟩
    | inv x _ hx => obtain ⟨i, rfl⟩ := hx; exact ⟨-i, by simp⟩
  have hDR : Derived (DihedralGroup 3) ≤ R := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a, b, rfl⟩
    obtain ⟨i, hi⟩ := mwt84_d3_comm a b
    rw [hi]; exact Subgroup.subset_closure ⟨i, rfl⟩
  -- commutators inside the derived subgroup are trivial
  have hcomm : ∀ a b : ↥(Derived (DihedralGroup 3)), a * b * a⁻¹ * b⁻¹ = 1 := by
    intro a b
    obtain ⟨i, hi⟩ := hR _ (hDR a.2)
    obtain ⟨j, hj⟩ := hR _ (hDR b.2)
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hi, hj, Subgroup.coe_one]
    simp [DihedralGroup.r_mul_r]
  have hbot : Derived (↥(Derived (DihedralGroup 3))) = ⊥ := by
    rw [eq_bot_iff]; apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a, b, rfl⟩; exact hcomm a b
  -- but the derived subgroup is nontrivial
  have hmem : (DihedralGroup.r 1 * DihedralGroup.sr 0 * (DihedralGroup.r 1)⁻¹ * (DihedralGroup.sr 0)⁻¹ :
      DihedralGroup 3) ∈ Derived (DihedralGroup 3) := Subgroup.subset_closure ⟨_, _, rfl⟩
  have : (⟨_, hmem⟩ : ↥(Derived (DihedralGroup 3))) ∈ (⊥ : Subgroup _) := by
    rw [← hbot, h]; trivial
  rw [Subgroup.mem_bot] at this
  have h2 : (DihedralGroup.r 1 * DihedralGroup.sr 0 * (DihedralGroup.r 1)⁻¹ * (DihedralGroup.sr 0)⁻¹ :
      DihedralGroup 3) = 1 := congrArg Subtype.val this
  revert h2; decide

theorem solution : ¬ (∀ {n k : ℕ} {G UW : Type} [Group G] [Group UW]
    (W : MultiWeldedTwinWorld n k G UW) (hn : 5 ≤ n),
    DerivedPerfect G) :=
  fun h => mwt84_perfect_false (h (mwt84_triv 5 1 one_pos (DihedralGroup 3)) le_rfl)
