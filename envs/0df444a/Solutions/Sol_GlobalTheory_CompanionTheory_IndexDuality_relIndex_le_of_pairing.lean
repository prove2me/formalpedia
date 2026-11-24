-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IndexDuality.relIndex_le_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:38:19.811386+00:00
-- url     : https://prove2.me/submissions/75085f03-7df1-4bfd-9e5a-1e801f4db2ca

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RelIndexOpenCompactNeZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCharacterSeparatingLattice
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RelIndexAnnihilatorsDuality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IndexDuality
namespace GlobalTheory.CompanionTheory.IndexDuality
theorem _root_.solution {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (b : X → Y → Circle)
    (hl : ∀ x x' y, b (x + x') y = b x y * b x' y)
    (hr : ∀ x y y', b x (y + y') = b x y * b x y')
    (H₀ H : AddSubgroup Y) (R₀ R : AddSubgroup X)
    (hfin : H₀.relIndex H ≠ 0)
    (hann : ∀ x ∈ R₀, ∀ y ∈ H₀, b x y = 1)
    (hsep : ∀ x ∈ R₀, (∀ y ∈ H, b x y = 1) → x ∈ R) :
    R.relIndex R₀ ≠ 0 ∧ R.relIndex R₀ ≤ H₀.relIndex H := by
  classical
  have hQfin : Finite (H ⧸ H₀.addSubgroupOf H) := Nat.finite_of_card_ne_zero hfin
  have hb0 : ∀ x, b x 0 = 1 := by
    intro x
    have h := hr x 0 0
    rw [add_zero] at h
    exact (mul_left_cancel (a := b x 0) (by rw [mul_one]; exact h)).symm
  have hb0' : ∀ y, b 0 y = 1 := by
    intro y
    have h := hl 0 0 y
    rw [add_zero] at h
    exact (mul_left_cancel (a := b 0 y) (by rw [mul_one]; exact h)).symm
  let f : R₀ → H →+ Additive Circle := fun x =>
    { toFun := fun y => Additive.ofMul (b x y)
      map_zero' := by simp [hb0]
      map_add' := fun y y' => by simp [hr] }
  have hker : ∀ x : R₀, ∀ y ∈ H₀.addSubgroupOf H, f x y = 0 := by
    intro x y hy
    rw [AddSubgroup.mem_addSubgroupOf] at hy
    simp [f, hann x x.2 y hy]
  let g : R₀ → (H ⧸ H₀.addSubgroupOf H) →+ Additive Circle := fun x =>
    QuotientAddGroup.lift (H₀.addSubgroupOf H) (f x) (hker x)
  let χ : R₀ → AddChar (H ⧸ H₀.addSubgroupOf H) Circle := fun x =>
    { toFun := fun q => Additive.toMul (g x q)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun q q' => by simp [map_add] }
  have hχ : ∀ (x : R₀) (y : H), χ x (QuotientAddGroup.mk y) = b x y := fun x y => rfl
  let Ψ : R₀ →+ AddChar (H ⧸ H₀.addSubgroupOf H) Circle :=
    { toFun := χ
      map_zero' := by
        ext1 q
        induction q using QuotientAddGroup.induction_on with
        | H y =>
          rw [hχ]
          exact hb0' y
      map_add' := fun x x' => by
        ext1 q
        induction q using QuotientAddGroup.induction_on with
        | H y =>
          rw [hχ]
          change b (x + x') y = (χ x * χ x') (QuotientAddGroup.mk y)
          rw [AddChar.mul_apply, hχ, hχ]
          exact hl x x' y }
  have hkerle : Ψ.ker ≤ R.addSubgroupOf R₀ := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    rw [AddSubgroup.mem_addSubgroupOf]
    refine hsep x x.2 (fun y hy => ?_)
    have := congrArg (fun φ : AddChar (H ⧸ H₀.addSubgroupOf H) Circle => φ (QuotientAddGroup.mk ⟨y, hy⟩)) hx
    simpa [Ψ, hχ] using this
  have : Fintype (H ⧸ H₀.addSubgroupOf H) := Fintype.ofFinite _
  have hinjC : Function.Injective fun φ : AddChar (H ⧸ H₀.addSubgroupOf H) Circle => Circle.coeHom.compAddChar φ :=
    MonoidHom.compAddChar_injective_right _ Circle.coe_injective
  have : Finite (AddChar (H ⧸ H₀.addSubgroupOf H) Circle) := Finite.of_injective _ hinjC
  have hcardC : Nat.card (AddChar (H ⧸ H₀.addSubgroupOf H) Circle) ≤ H₀.relIndex H := by
    have h1 := Nat.card_le_card_of_injective _ hinjC
    rw [Nat.card_eq_fintype_card (α := AddChar (H ⧸ H₀.addSubgroupOf H) ℂ), AddChar.card_eq,
      ← Nat.card_eq_fintype_card] at h1
    exact h1
  have : Finite (R₀ ⧸ Ψ.ker) := Finite.of_injective _ (QuotientAddGroup.kerLift_injective Ψ)
  have hkerfin : Ψ.ker.index ≤ Nat.card (AddChar (H ⧸ H₀.addSubgroupOf H) Circle) :=
    Nat.card_le_card_of_injective _ (QuotientAddGroup.kerLift_injective Ψ)
  have hker0 : Ψ.ker.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have hdvd := AddSubgroup.index_dvd_of_le hkerle
  have hR0 : (R.addSubgroupOf R₀).index ≠ 0 := fun h0 => hker0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  refine ⟨hR0, ?_⟩
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hker0) hdvd).trans (hkerfin.trans hcardC)
end GlobalTheory.CompanionTheory.IndexDuality
