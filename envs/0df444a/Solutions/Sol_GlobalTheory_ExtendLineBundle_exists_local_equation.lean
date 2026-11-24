-- Prove2me | solution 1 for GlobalTheory.ExtendLineBundle.exists_local_equation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:13:43.547892+00:00
-- url     : https://prove2.me/submissions/4bb3490d-1d96-4409-9b4a-1580064d4ecf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_GlobalTheory_ExtendLineBundle_germ_mem
import Theorems.Thm_GlobalTheory_ExtendLineBundle_eventually_mem
import Theorems.Thm_GlobalTheory_ExtendLineBundle_exists_pow_mul_mem
import Theorems.Thm_GlobalTheory_ExtendLineBundle_inv_germ_mem
import Theorems.Thm_GlobalTheory_ExtendLineBundle_exists_gcd_fraction
import Theorems.Thm_GlobalTheory_ExtendLineBundle_mem_localUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
noncomputable section
open GlobalTheory GlobalTheory.ExtendLineBundle
variable {X Y : Scheme.{0}} [IsIntegral X]
namespace GlobalTheory.ExtendLineBundle
theorem _root_.solution [NoetherianSpace X] {T : Set (X.Opens × X.functionFieldˣ)}
    (hT : Compatible T) (x : X) [UniqueFactorizationMonoid (X.presheaf.stalk x)] :
    ∃ (W : X.Opens) (h : X.functionFieldˣ), x ∈ W ∧
      ∀ p ∈ T, ∀ y, y ∈ W → y ∈ p.1 → h / p.2 ∈ localUnits y := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hη : genericPoint X ∈ U := genericPoint_mem hxU
  let C : Set X := {y | y ∈ U ∧ ∃ p ∈ T, y ∈ p.1}
  have hC : ∀ y : C, ∃ p ∈ T, ∃ a : Γ(X, U), X.basicOpen a ≤ p.1 ∧ y.1 ∈ X.basicOpen a := by
    rintro ⟨y, hy, p, hp, hyp⟩
    obtain ⟨a, ha, hya⟩ := IsAffineOpen.exists_basicOpen_le hU (V := p.1) ⟨y, hyp⟩ hy
    exact ⟨p, hp, a, ha, hya⟩
  choose P hP a ha hya using hC
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact C).elim_finite_subcover
    (fun y : C => (X.basicOpen (a y) : Set X)) (fun y => (X.basicOpen (a y)).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hya _⟩)
  let α : t → X.functionField := fun k => X.presheaf.germ U _ hη (a k)
  let f : t → X.functionField := fun k => (P k).2
  have hα : ∀ k, α k ≠ 0 := fun k => (inv_germ_mem _ hη (hya k)).1
  have hf : ∀ k, f k ≠ 0 := fun k => Units.ne_zero _
  have h1 : ∀ kl : t × t, ∃ n : ℕ, (α kl.1 * α kl.2) ^ n * (f kl.1 / f kl.2) ∈ localSubring x := by
    rintro ⟨k, l⟩
    obtain ⟨n, hn⟩ := exists_pow_mul_mem hU (a k * a l) hη (t := f k / f l)
      (by rw [Scheme.basicOpen_mul]; exact ⟨genericPoint_mem (hya _), genericPoint_mem (hya _)⟩)
      (fun y hy => by
        rw [Scheme.basicOpen_mul] at hy
        have := (mem_localUnits.1 (hT _ (hP k) _ (hP l) y (ha _ hy.1) (ha _ hy.2))).1
        rwa [Units.val_div_eq_div_val] at this)
    refine ⟨n, ?_⟩
    have := hn x hxU
    rwa [map_mul] at this
  choose n hn using h1
  obtain ⟨N, hN⟩ := (Set.finite_range n).bddAbove
  have h2 : ∀ k l, (α k ^ N * f k) * (α l ^ N / f l) ∈ localSubring x := fun k l => by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (hN ⟨(k, l), rfl⟩)
    have := mul_mem (pow_mem (mul_mem (germ_mem hxU hη (a k)) (germ_mem hxU hη (a l))) m)
      (hn (k, l))
    convert this using 1
    change _ = (α k * α l) ^ m * _
    rw [hm]
    ring
  obtain ⟨h, h0, h3, h4⟩ := exists_gcd_fraction (R := X.presheaf.stalk x)
    (fun k => α k ^ N * f k) (fun k => mul_ne_zero (pow_ne_zero _ (hα k)) (hf k))
  have h5 : ∀ᶠ y in nhds x, ∀ k, α k ^ N * f k / h ∈ localSubring y ∧
      h * (α k ^ N / f k) ∈ localSubring y :=
    Filter.eventually_all.2 fun k =>
      (eventually_mem (h3 k)).and (eventually_mem (h4 _ ⟨k⟩ fun l => h2 l k))
  obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.1 h5
  refine ⟨⟨W, hWo⟩ ⊓ U, Units.mk0 h h0, ⟨hxW, hxU⟩, fun p hp y hy hyp => ?_⟩
  obtain ⟨k, hk, hyk⟩ := Set.mem_iUnion₂.1 (ht (show y ∈ C from ⟨hy.2, p, hp, hyp⟩))
  have hi : (α ⟨k, hk⟩ ^ N)⁻¹ ∈ localSubring y := by
    rw [← inv_pow]
    exact pow_mem (inv_germ_mem _ hη hyk).2 N
  obtain ⟨h6, h7⟩ := hW y hy.1 ⟨k, hk⟩
  have h8 : Units.mk0 h h0 / (P k).2 ∈ localUnits y := by
    rw [mem_localUnits, Units.val_div_eq_div_val]
    have := pow_ne_zero N (hα ⟨k, hk⟩)
    have := hf ⟨k, hk⟩
    constructor
    · convert mul_mem hi h7 using 1
      change h / f ⟨k, hk⟩ = _
      field_simp
    · convert mul_mem hi h6 using 1
      change (h / f ⟨k, hk⟩)⁻¹ = _
      field_simp
  have := mul_mem h8 (hT _ (hP k) _ hp y (ha _ hyk) hyp)
  rwa [div_mul_div_cancel] at this
end GlobalTheory.ExtendLineBundle
