-- Prove2me | solution 1 for GlobalTheory.HilbFam.exists_eq_split_of_hasLevel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:30:48.045495+00:00
-- url     : https://prove2.me/submissions/352d12b3-54b6-4984-af53-86e2873a4213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSplitOfHilbertLatticeHasLevel
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_latM_eq_dual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam
variable {F : Type} [Field F] [NumberField F]
set_option autoImplicit false
open NumberField UpperHalfPlane
open scoped Classical MatrixGroups nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HilbFam
namespace _root_.GlobalTheory.HilbFam
theorem _root_.solution (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F) (hN : 0 < N) (hL : _root_.GlobalTheory.HilbFam.HasLevel N L) :
    ∃ (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (x : F), L = _root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x := by
  obtain ⟨hNL, hLstd⟩ := hL
  have hLint : ∀ v ∈ L, ∀ i, v i ∈ (1 : Submodule (𝓞 F) F) := fun v hv i =>
    (Submodule.mem_pi.1 (hLstd hv)) i (Set.mem_univ i)
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hsingle : ∀ i, Pi.single i (N : F) ∈ L := by
    intro i
    have hstd : (Pi.single i (1 : F) : Fin 2 → F) ∈ _root_.GlobalTheory.HilbFam.stdLat F := by
      refine Submodule.mem_pi.2 fun j _ => ?_
      by_cases hj : j = i
      · subst hj; simpa using (1 : Submodule (𝓞 F) F).one_le.1 le_rfl
      · simp [hj]
    have := hNL _ hstd
    convert this using 1
    ext j
    by_cases hj : j = i
    · subst hj
      simp [Algebra.smul_def]
    · simp [hj]
  let B0 : Submodule (𝓞 F) F := L.map (LinearMap.proj (R := 𝓞 F) (φ := fun _ : Fin 2 => F) 0)
  let C0 : Submodule (𝓞 F) F := L.comap (LinearMap.single (𝓞 F) (fun _ : Fin 2 => F) 1)
  have hB0 : B0 ≤ 1 := by
    rintro _ ⟨v, hv, rfl⟩
    exact hLint v hv 0
  have hC0 : C0 ≤ 1 := by
    intro c hc
    simpa using hLint _ hc 1
  let Bf : FractionalIdeal (𝓞 F)⁰ F := ⟨B0, FractionalIdeal.isFractional_of_le_one B0 hB0⟩
  let Cf : FractionalIdeal (𝓞 F)⁰ F := ⟨C0, FractionalIdeal.isFractional_of_le_one C0 hC0⟩
  have hBne : Bf ≠ 0 := by
    intro h
    have hmem : (N : F) ∈ Bf := by
      show (N : F) ∈ B0
      exact ⟨_, hsingle 0, by simp⟩
    rw [h] at hmem
    exact hN0 ((FractionalIdeal.mem_zero_iff _).1 hmem)
  have hCne : Cf ≠ 0 := by
    intro h
    have hmem : (N : F) ∈ Cf := by
      show Pi.single 1 (N : F) ∈ L
      exact hsingle 1
    rw [h] at hmem
    exact hN0 ((FractionalIdeal.mem_zero_iff _).1 hmem)
  have key : ∀ t ∈ (Bf : Submodule (𝓞 F) F) * ((Bf⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F),
      ∃ y : F, ∀ b ∈ Bf, (![t * b, y * b] : Fin 2 → F) ∈ L := by
    intro t ht
    refine Submodule.mul_induction_on ht ?_ ?_
    · intro b' hb' c hc
      obtain ⟨w, hw, hw0⟩ := (show b' ∈ B0 from hb')
      refine ⟨c * w 1, fun b hb => ?_⟩
      have hcb : c * b ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
        rw [← inv_mul_cancel₀ hBne]
        exact FractionalIdeal.mul_mem_mul hc hb
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hcb
      convert L.smul_mem r hw using 1
      ext i
      fin_cases i
      · simp [Algebra.smul_def, hr, ← hw0]
        ring
      · simp [Algebra.smul_def, hr]
        ring
    · rintro t₁ t₂ ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩
      refine ⟨y₁ + y₂, fun b hb => ?_⟩
      convert L.add_mem (hy₁ b hb) (hy₂ b hb) using 1
      ext i
      fin_cases i <;> simp <;> ring
  have h1 : (1 : F) ∈ (Bf : Submodule (𝓞 F) F) *
      ((Bf⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hBne]
    exact FractionalIdeal.one_mem_one _
  obtain ⟨x, hx⟩ := key 1 h1
  refine ⟨Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne),
    Units.mk0 Bf hBne, x, ?_⟩
  have hlat : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM
      (Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne)) = Cf := by
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, Units.val_mk0, FractionalIdeal.dual_dual]
  ext v
  unfold _root_.GlobalTheory.HilbFam.split
  rw [Submodule.mem_mk]
  change v ∈ L ↔ v 0 ∈ ((Units.mk0 Bf hBne : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ∧
    v 1 - v 0 * x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM
      (Units.mk0 (FractionalIdeal.dual ℤ ℚ Cf) (FractionalIdeal.dual_ne_zero ℤ ℚ hCne))
  rw [hlat, Units.val_mk0]
  change v ∈ L ↔ v 0 ∈ B0 ∧ Pi.single 1 (v 1 - v 0 * x) ∈ L
  constructor
  · intro hv
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    convert L.sub_mem hv (hx (v 0) ⟨v, hv, rfl⟩) using 1
    ext i
    fin_cases i <;> simp <;> ring
  · rintro ⟨hb, hc⟩
    convert L.add_mem (hx (v 0) hb) hc using 1
    ext i
    fin_cases i <;> simp <;> ring
end _root_.GlobalTheory.HilbFam
end GlobalTheory.HilbFam
