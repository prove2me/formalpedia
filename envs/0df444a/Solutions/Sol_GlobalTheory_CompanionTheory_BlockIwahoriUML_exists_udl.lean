-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BlockIwahoriUML.exists_udl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:15:14.566952+00:00
-- url     : https://prove2.me/submissions/63bf51bf-45d2-49bd-9186-c030ff1e3f6f

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsPrincipalCongruence
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriBlockUpperLeviLower
import Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_exists_udl_of_isUnit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BlockIwahoriUML
variable {k Γ : Type*} [Field k] [LinearOrderedCommGroupWithZero Γ]
namespace GlobalTheory.CompanionTheory.BlockIwahoriUML
theorem _root_.solution (v : Valuation k Γ) {r : Γ} (hr : r < 1) (n : ℕ)
    (g : Matrix (Fin n) (Fin n) k) (hg : Cong v r g) :
    ∃ u d l : Matrix (Fin n) (Fin n) k, Cong v r u ∧ Cong v r l ∧
      (∀ i j, j < i → u i j = 0) ∧ (∀ i, u i i = 1) ∧ (∀ i j, i ≠ j → d i j = 0) ∧
      (∀ i j, i < j → l i j = 0) ∧ (∀ i, l i i = 1) ∧ g = u * d * l := by
  classical
  let I : Ideal v.integer :=
    { carrier := {x | v (x : k) ≤ r}
      add_mem' := fun {a b} ha hb => by
        have := Valuation.map_add_le v ha hb
        simpa using this
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        have hc : v (c : k) ≤ 1 := c.2
        have hx' : v (x : k) ≤ r := hx
        show v ((c * x : v.integer) : k) ≤ r
        rw [Subring.coe_mul, map_mul]
        calc v (c : k) * v (x : k) ≤ 1 * r := mul_le_mul' hc hx'
          _ = r := one_mul r }
  have hImem : ∀ x : v.integer, x ∈ I ↔ v (x : k) ≤ r := fun x => Iff.rfl
  have hI : ∀ x ∈ I, IsUnit (1 + x) := by
    intro x hx
    have hx' : v (x : k) < 1 := lt_of_le_of_lt ((hImem x).1 hx) hr
    have h1 : v (1 + (x : k)) = 1 := Valuation.map_one_add_of_lt v hx'
    have h0 : (1 + (x : k)) ≠ 0 := by
      intro h
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    have hmem : (1 + (x : k))⁻¹ ∈ v.integer := by
      show v _ ≤ 1
      rw [map_inv₀, h1, inv_one]
    refine isUnit_iff_exists_inv.2 ⟨⟨(1 + (x : k))⁻¹, hmem⟩, Subtype.ext ?_⟩
    simpa using mul_inv_cancel₀ h0
  have hone : ∀ i j, v ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have hint : ∀ i j, v (g i j) ≤ 1 := by
    intro i j
    have := Valuation.map_add_le v ((hg i j).trans hr.le) (hone i j)
    simpa using this
  let g' : Matrix (Fin n) (Fin n) v.integer := fun i j => ⟨g i j, hint i j⟩
  have hone' : ∀ i j, (((1 : Matrix (Fin n) (Fin n) v.integer) i j : v.integer) : k) =
      (1 : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have hg' : ∀ i j, g' i j - (1 : Matrix (Fin n) (Fin n) v.integer) i j ∈ I := by
    intro i j
    rw [hImem, AddSubgroupClass.coe_sub, hone']
    exact hg i j
  obtain ⟨u, d, l, hu, hd, hl, h⟩ := IwahoriUDL.exists_udl_of_isUnit I hI n g' hg'
  have back : ∀ a : Matrix (Fin n) (Fin n) v.integer,
      (∀ i j, a i j - (1 : Matrix (Fin n) (Fin n) v.integer) i j ∈ I) →
        Cong v r (a.map v.integer.subtype) := by
    intro a ha i j
    have := (hImem _).1 (ha i j)
    rw [AddSubgroupClass.coe_sub, hone'] at this
    exact this
  refine ⟨u.map v.integer.subtype, d.map v.integer.subtype, l.map v.integer.subtype,
    back u hu.1, back l hl.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    simp [hu.2.1 i j hij]
  · intro i
    simp [hu.2.2 i]
  · intro i j hij
    simp [hd.2 i j hij]
  · intro i j hij
    simp [hl.2.1 i j hij]
  · intro i
    simp [hl.2.2 i]
  · have hgg : g = g'.map v.integer.subtype := by
      ext i j
      rfl
    rw [hgg, h, Matrix.map_mul, Matrix.map_mul]
end GlobalTheory.CompanionTheory.BlockIwahoriUML
