-- Prove2me | solution 1 for GlobalTheory.cube_trivialisation_on_uniformising_space
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:48.273029+00:00
-- url     : https://prove2.me/submissions/2f3ebe64-6c08-46f8-8df1-62f35ae7aee2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_inf
import Theorems.Thm_GlobalTheory_CubeValues_val_unit_ne_zero
import Theorems.Thm_GlobalTheory_CubeValues_le_preimage_wchart
import Theorems.Thm_GlobalTheory_CubeValues_val_gen
import Theorems.Thm_GlobalTheory_CubeValues_val_linComb
import Theorems.Thm_GlobalTheory_CubeValues_val_cocycle
import Theorems.Thm_GlobalTheory_CubeValues_ex_add_period
import Theorems.Thm_GlobalTheory_CubeValues_tripleProductPoint_comp_partialSum
import Theorems.Thm_GlobalTheory_CubeValues_tripleProductPoint_add_period
import Theorems.Thm_GlobalTheory_CubeValues_hol_coord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
namespace GlobalTheory.CubeValues
section Values
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)
end Values
section Points
variable {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left} {g : ℕ} (u : HolUnif A L₀ g)
private theorem pt3_preimage_theta_whole_iff {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left} {g : ℕ}
    (u : HolUnif A L₀ g) (L : LB A.left) (j : Finset (Fin 3) → L.ι) (x : Fin 3 → Fin g → ℂ) :
    ⊤ ≤ (pt3 u x).left ⁻¹ᵁ (Theta A L).U (fun I => j I.down) ↔
      ∀ I : Finset (Fin 3), ⊤ ≤ (u.ex (∑ a ∈ I, x a)).left ⁻¹ᵁ L.U (j I) := by
  show ⊤ ≤ (pt3 u x).left ⁻¹ᵁ
      L.wchart (fun I : ULift (Finset (Fin 3)) => (psum A (x3 A) I.down).left) (fun I => j I.down) ↔ _
  rw [le_preimage_wchart]
  simp only [tripleProductPoint_comp_partialSum]
  exact ⟨fun h I => h ⟨I⟩, fun h I => h I.down⟩
private theorem valAt_theta_transition_eq_prod_zpow (hv : ValueRules) {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left}
    {g : ℕ} (u : HolUnif A L₀ g) (L : LB A.left) (j j' : Finset (Fin 3) → L.ι) (x : Fin 3 → Fin g → ℂ)
    (hj : ⊤ ≤ (pt3 u x).left ⁻¹ᵁ (Theta A L).U (fun I => j I.down))
    (hj' : ⊤ ≤ (pt3 u x).left ⁻¹ᵁ (Theta A L).U (fun I => j' I.down)) :
    valAt' (pt3 u x).left ((Theta A L).U (fun I => j I.down) ⊓ (Theta A L).U (fun I => j' I.down))
        ((Theta A L).g (fun I => j I.down) (fun I => j' I.down)).val =
      ∏ I : Finset (Fin 3), valAt' (u.ex (∑ a ∈ I, x a)).left (L.U (j I) ⊓ L.U (j' I))
        (L.g (j I) (j' I)).val ^ ((-1 : ℤ) ^ (3 - I.card)) := by
  have e := val_linComb (pt3 u x).left hv L
    (fun I : ULift (Finset (Fin 3)) => (psum A (x3 A) I.down).left)
    (fun I : ULift (Finset (Fin 3)) => (-1 : ℤ) ^ (3 - I.down.card)) (fun I => j I.down) (fun I => j' I.down) hj hj'
  simp only [tripleProductPoint_comp_partialSum] at e
  refine e.trans ?_
  exact Fintype.prod_equiv Equiv.ulift _ _ (fun _ => rfl)
end Points
end GlobalTheory.CubeValues
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory.CubeValues
namespace GlobalTheory
theorem _root_.solution :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w)) w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) → (∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (L₀ L : LB A.left) (g : ℕ) (u : HolUnif A L₀ g), L.IsLB → ∀ t : LB.Gen (Theta A L), t.IsGen → ∀ (W : L.ι → Set (Fin g → ℂ)) (c : L.ι → L.ι → (Fin g → ℂ) → ℂ), W = (fun (i : L.ι) => {z : Fin g → ℂ | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i}) → c = (fun (i j : L.ι) (z : Fin g → ℂ) => valAt' (u.ex z).left (L.U i ⊓ L.U j) (L.g i j).val) → ((∀ i, IsOpen (W i)) ∧ (∀ z, ∃ i, z ∈ W i) ∧ (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) ∧ (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) ∧ (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) ∧ (∀ i z, ∀ l ∈ u.Λ, z + l ∈ W i ↔ z ∈ W i) ∧ (∀ i j z, ∀ l ∈ u.Λ, c i j (z + l) = c i j z)) ∧ ∃ T : (Finset (Fin 3) → L.ι) → (Fin 3 → Fin g → ℂ) → ℂ, (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) ∧ (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) ∧ (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) ∧ (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ u.Λ) → T j (x + l) = T j x)) := by
  intro hv0 hlift A _ _ L₀ L g u hL t ht W c hW hc
  have hv : ValueRules := hv0
  subst hW hc
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact (u.hol (L.U i) 0).1
  · intro z
    have hq : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by
      rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hq
    exact ⟨i, ((hv _ (u.ex z).left).1 (L.U i)).2 hi⟩
  · intro i j
    have hset : ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i} ∩ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j}) =
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U j)} := by
      ext z
      exact (le_preimage_inf _ _ _).symm
    show DifferentiableOn ℂ (fun z => valAt' (u.ex z).left (L.U i ⊓ L.U j) (L.g i j).val)
      ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i} ∩ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j})
    rw [hset]
    exact (u.hol _ _).2
  · intro i j z hi hj
    exact val_unit_ne_zero _ hv ((le_preimage_inf _ _ _).2 ⟨hi, hj⟩) _
  · intro i j k z hi hj hk
    exact val_cocycle _ hv hL i j k hi hj hk
  · intro i z l hl
    show ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i ↔ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i
    rw [ex_add_period u z l hl]
  · intro i j z l hl
    show valAt' (u.ex (z + l)).left _ _ = valAt' (u.ex z).left _ _
    rw [ex_add_period u z l hl]
  · have hH := hlift (Fin 3 → Fin g → ℂ) Set.univ A (A ⊗ A) (fun w => u.ex (w 0))
      (fun w => lift (u.ex (w 1)) (u.ex (w 2))) (fun U f => hol_coord u 0 U f)
      (hlift (Fin 3 → Fin g → ℂ) Set.univ A A (fun w => u.ex (w 1)) (fun w => u.ex (w 2))
        (fun U f => hol_coord u 1 U f) (fun U f => hol_coord u 2 U f))
    refine ⟨fun j x => valAt' (pt3 u x).left ((Theta A L).U (fun I => j I.down)) (t.s (fun I => j I.down)).val,
      ?_, ?_, ?_, ?_⟩
    · intro j
      refine ((hH ((Theta A L).U (fun I => j I.down)) (t.s (fun I => j I.down)).val).2).mono ?_
      intro x hx
      exact ⟨trivial, (GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j x).2 hx⟩
    · intro j x hx
      exact val_unit_ne_zero _ hv ((GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j x).2 hx) _
    · intro j j' x hx hx'
      have hi := (GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j x).2 hx
      have hi' := (GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j' x).2 hx'
      have e := val_gen (pt3 u x).left hv t ht _ _ hi hi'
      rw [GlobalTheory.CubeValues.valAt_theta_transition_eq_prod_zpow hv u L j j' x hi hi'] at e
      exact e
    · intro j x l hl
      show valAt' (pt3 u (x + l)).left _ _ = valAt' (pt3 u x).left _ _
      rw [tripleProductPoint_add_period u x l hl]
end GlobalTheory
