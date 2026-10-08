-- Prove2me | solution 1 for MDPFinance.StructuredModels.concave_preserved
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:01:11.041719+00:00
-- url     : https://prove2.me/submissions/40d71b4d-b237-4354-9ef7-b6ef2cd572fe

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_BoundingFunction
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators
import Definitions.Def_MDPFinance_StructuredModels_ConvexAnalysis

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace F4ea04ffAux

theorem coe_mul_biSup_le {ι : Type*} (s : Set ι) (f : ι → EReal) {α : ℝ} (hα : 0 < α) :
    (α : EReal) * (⨆ i ∈ s, f i) ≤ ⨆ i ∈ s, (α : EReal) * f i := by
  have hinv : ∀ t : EReal, ((α⁻¹ : ℝ) : EReal) * ((α : EReal) * t) = t := by
    intro t
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ hα.ne', EReal.coe_one, one_mul]
  have hinv' : ∀ t : EReal, (α : EReal) * (((α⁻¹ : ℝ) : EReal) * t) = t := by
    intro t
    rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hα.ne', EReal.coe_one, one_mul]
  have h0 : (0 : EReal) ≤ ((α⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_pos.2 hα).le
  have h0' : (0 : EReal) ≤ (α : EReal) := by exact_mod_cast hα.le
  have key : (⨆ i ∈ s, f i) ≤ ((α⁻¹ : ℝ) : EReal) * ⨆ i ∈ s, (α : EReal) * f i := by
    refine iSup₂_le fun i hi => ?_
    calc f i = ((α⁻¹ : ℝ) : EReal) * ((α : EReal) * f i) := (hinv _).symm
      _ ≤ ((α⁻¹ : ℝ) : EReal) * ⨆ i ∈ s, (α : EReal) * f i :=
        mul_le_mul_of_nonneg_left (le_iSup₂ (f := fun i (_ : i ∈ s) => (α : EReal) * f i) i hi) h0
  calc (α : EReal) * (⨆ i ∈ s, f i)
      ≤ (α : EReal) * (((α⁻¹ : ℝ) : EReal) * ⨆ i ∈ s, (α : EReal) * f i) :=
        mul_le_mul_of_nonneg_left key h0'
    _ = _ := hinv' _

end F4ea04ffAux

open MDPFinance.StructuredModels in
theorem solution {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup A] [Module ℝ A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (b : E → ℝ) (cr cg αb : ℝ)
    (hb : IsUpperBoundingFunction M b cr cg αb) (n : ℕ) (hn : n < N)
    (v : E → EReal) (hv : v ∈ IBbPlus b)
    (hD_convex : Convex ℝ (M.D n))
    (hL_concave : ConcaveOnEReal (M.D n) (L M n v)) :
    ConcaveOnEReal Set.univ (T M n v) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ α β hα hβ hαβ
  rcases hα.eq_or_lt with h | hαpos
  · subst h
    have hβ1 : β = 1 := by linarith
    subst hβ1
    simp
  rcases hβ.eq_or_lt with h | hβpos
  · subst h
    have hα1 : α = 1 := by linarith
    subst hα1
    simp
  set z := α • x + β • y
  calc (α : EReal) * T M n v x + (β : EReal) * T M n v y
      ≤ (⨆ a ∈ M.Dx n x, (α : EReal) * L M n v (x, a)) +
          (⨆ a ∈ M.Dx n y, (β : EReal) * L M n v (y, a)) :=
        add_le_add (F4ea04ffAux.coe_mul_biSup_le _ _ hαpos)
          (F4ea04ffAux.coe_mul_biSup_le _ _ hβpos)
    _ ≤ T M n v z := by
        refine EReal.add_le_of_forall_lt fun p hp q hq => ?_
        obtain ⟨a1, ha1, hp1⟩ := lt_biSup_iff.1 hp
        obtain ⟨a2, ha2, hq2⟩ := lt_biSup_iff.1 hq
        have hmem : (z, α • a1 + β • a2) ∈ M.D n := by
          have := hD_convex ha1 ha2 hα hβ hαβ
          simpa [z, Prod.smul_mk, Prod.mk_add_mk] using this
        have hconc := hL_concave.2 ha1 ha2 hα hβ hαβ
        have heq : α • ((x, a1) : E × A) + β • (y, a2) = (z, α • a1 + β • a2) := by
          simp [z, Prod.smul_mk, Prod.mk_add_mk]
        rw [heq] at hconc
        calc p + q ≤ (α : EReal) * L M n v (x, a1) + (β : EReal) * L M n v (y, a2) :=
              add_le_add hp1.le hq2.le
          _ ≤ L M n v (z, α • a1 + β • a2) := hconc
          _ ≤ T M n v z :=
              le_iSup₂ (f := fun a (_ : a ∈ M.Dx n z) => L M n v (z, a)) (α • a1 + β • a2) hmem
