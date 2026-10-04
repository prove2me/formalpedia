-- Prove2me | solution 1 for Matrix.card_sub_one_le_rank_of_charSum_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T09:31:23.003793+00:00
-- url     : https://prove2.me/submissions/95cc0954-e958-4ec4-9c0f-a9930c7e80c3

import Mathlib

/-- The number of characters `G →* Fˣ` of a finite commutative group equals `|G|`. -/
lemma card_monoidHom_units_of_hasEnoughRootsOfUnity_card
    {G : Type*} [CommGroup G] [Fintype G] {F : Type*} [Field F]
    [HasEnoughRootsOfUnity F (Fintype.card G)] :
    Nat.card (G →* Fˣ) = Fintype.card G := by
  have : NeZero (Fintype.card G) := ⟨Fintype.card_ne_zero⟩
  have : HasEnoughRootsOfUnity F (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd F Group.exponent_dvd_card
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_eq_fintype_card]

theorem solution
    {G : Type*} [Group G] [IsMulCommutative G] [Fintype G]
    {F : Type*} [Field F] [HasEnoughRootsOfUnity F (Fintype.card G)]
    (f : G → F)
    (hf : ∀ χ : G →* Fˣ, χ ≠ 1 → ∑ σ, ((χ σ : Fˣ) : F) * f σ ≠ 0) :
    Fintype.card G - 1 ≤ (Matrix.of fun σ τ : G => f (σ * τ⁻¹)).rank := by
  classical
  -- Step 5 (count of characters).
  let : CommGroup G := { ‹Group G› with mul_comm := fun a b => mul_comm' a b }
  have hcardchar : Nat.card (G →* Fˣ) = Fintype.card G :=
    card_monoidHom_units_of_hasEnoughRootsOfUnity_card
  have : NeZero (Fintype.card G) := ⟨Fintype.card_ne_zero⟩
  have : HasEnoughRootsOfUnity F (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd F Group.exponent_dvd_card
  let : Fintype (G →* Fˣ) := Fintype.ofFinite _
  set M : Matrix G G F := Matrix.of fun σ τ : G => f (σ * τ⁻¹) with hM
  let x : (G →* Fˣ) → G → F := fun χ τ => ((χ τ⁻¹ : Fˣ) : F)
  let S : (G →* Fˣ) → F := fun χ => ∑ ρ, ((χ ρ : Fˣ) : F) * f ρ
  -- Step 2: eigenvector equation.
  have heig : ∀ χ, M.mulVec (x χ) = S χ • x χ := by
    intro χ
    ext σ
    simp only [hM, x, S, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply,
      smul_eq_mul, Finset.sum_mul]
    refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulLeft σ)) _ _ ?_
    intro τ
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft, map_mul, Units.val_mul]
    have h1 : ((χ σ⁻¹ : Fˣ) : F) * ((χ σ : Fˣ) : F) = 1 := by
      rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    linear_combination -(f (σ * τ⁻¹) * ((χ τ⁻¹ : Fˣ) : F)) * h1
  -- Step 3: range membership.
  have hmem : ∀ χ : G →* Fˣ, χ ≠ 1 → x χ ∈ LinearMap.range M.mulVecLin := by
    intro χ hχ
    refine ⟨(S χ)⁻¹ • x χ, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_smul, heig, smul_smul,
      inv_mul_cancel₀ (hf χ hχ), one_smul]
  -- Step 4: linear independence (Dedekind).
  let ψ : (G →* Fˣ) → (G →* F) := fun χ => (Units.coeHom F).comp χ⁻¹
  have hx : ∀ χ, (ψ χ : G → F) = x χ := by
    intro χ
    ext τ
    simp [ψ, x, map_inv]
  have hψinj : Function.Injective ψ := by
    intro χ₁ χ₂ h
    have : χ₁⁻¹ = χ₂⁻¹ := by
      ext τ
      have := DFunLike.congr_fun h τ
      simpa [ψ] using this
    exact inv_injective this
  have hli : LinearIndependent F (fun χ : {χ : G →* Fˣ // χ ≠ 1} => x χ.1) := by
    have h1 := (linearIndependent_monoidHom G F).comp ψ hψinj
    have h2 := h1.comp (Subtype.val : {χ : G →* Fˣ // χ ≠ 1} → _) Subtype.val_injective
    have e : (fun χ : {χ : G →* Fˣ // χ ≠ 1} => x χ.1) =
        ((fun φ : G →* F => (φ : G → F)) ∘ ψ) ∘ Subtype.val := by
      funext χ
      exact (hx χ.1).symm
    rw [e]
    exact h2
  -- Step 6: conclude.
  let R := LinearMap.range M.mulVecLin
  let y : {χ : G →* Fˣ // χ ≠ 1} → R := fun χ => ⟨x χ.1, hmem χ.1 χ.2⟩
  have hliy : LinearIndependent F y := LinearIndependent.of_comp R.subtype hli
  have hcard := hliy.fintype_card_le_finrank
  have hc : Fintype.card {χ : G →* Fˣ // χ ≠ 1} = Fintype.card G - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      hcardchar]
  show Fintype.card G - 1 ≤ Module.finrank F (LinearMap.range M.mulVecLin)
  rw [← hc]
  exact hcard
