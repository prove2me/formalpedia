-- Prove2me | solution 1 for NumberField.tprod_inv_eulerFactor_mul_tprod_eulerFactor_eq_prod_sdiff_of_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b9981f05-4b3b-5fea-a456-0f1d1d28e321

import Mathlib
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_tprod_inv_eulerFactor_mul_tprod_eulerFactor_eq_prod_sdiff_of_norm_le_one

set_option autoImplicit false

open IsDedekindDomain NumberField Filter Topology
open scoped Classical

namespace EulerSetChange

variable {F : Type} [Field F] [NumberField F]

private theorem hasProd_inv₀ {ι : Type*} {f : ι → ℂ} {a : ℂ} (hf : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  have h : (fun s : Finset ι => ∏ b ∈ s, (f b)⁻¹) = fun s => (∏ b ∈ s, f b)⁻¹ := by
    funext s
    exact Finset.prod_inv_distrib (f := f) (s := s)
  unfold HasProd at hf ⊢
  rw [h]
  exact hf.inv₀ ha

private theorem multipliable_and_tprod_eq_and_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F)))
    (z : HeightOneSpectrum (𝓞 F) → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    Multipliable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
        (1 - z v.1 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) ∧
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, (1 - z v.1 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))
      = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
          (1 - z v.1 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)⁻¹ ∧
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
        (1 - z v.1 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) ≠ 0 := by
  obtain ⟨hE1, -, hE3⟩ :=
    NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one F S (fun v => z v.1)
      (fun v => hz v.1)
  obtain ⟨a, ha⟩ := hE1 s hs
  have ha0 : a ≠ 0 := by rw [← ha.tprod_eq]; exact hE3 s hs
  have hinv := hasProd_inv₀ ha ha0
  simp only [inv_inv] at hinv
  exact ⟨hinv.multipliable, by rw [hinv.tprod_eq, ha.tprod_eq], hE3 s hs⟩

private theorem T1E_aux {X : Type*} (T : Set X) (g : X → ℂ) (hT : Multipliable (g ∘ ((↑) : T → X)))
    (hc : Multipliable (g ∘ ((↑) : ↥Tᶜ → X))) :
    (∏' x : T, g x) * (∏' x : ↥Tᶜ, g x) = ∏' x, g x := hT.tprod_mul_tprod_compl hc

private theorem T1E_tprod_split (ST S : Finset (HeightOneSpectrum (𝓞 F))) (hST : ST ⊆ S)
    (f : HeightOneSpectrum (𝓞 F) → ℂ)
    (hS : Multipliable (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => f v.1)) :
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ ST}, f v.1)
      = (∏ v ∈ S \ ST, f v) * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, f v.1 := by
  obtain ⟨T, hT⟩ : ∃ T : Set {v : HeightOneSpectrum (𝓞 F) // v ∉ ST}, T = {x | x.1 ∈ S} := ⟨_, rfl⟩
  have hmemT : ∀ x : {v : HeightOneSpectrum (𝓞 F) // v ∉ ST}, x ∈ T ↔ x.1 ∈ S := fun x => by rw [hT]; rfl
  have hmemc : ∀ x : {v : HeightOneSpectrum (𝓞 F) // v ∉ ST}, x ∈ Tᶜ ↔ x.1 ∉ S := fun x => by
    rw [Set.mem_compl_iff, hmemT]
  have hTfin : T.Finite := by
    refine Set.Finite.of_finite_image (f := fun x : {v : HeightOneSpectrum (𝓞 F) // v ∉ ST} => x.1) ?_
      Subtype.val_injective.injOn
    exact S.finite_toSet.subset (by rintro _ ⟨x, hx, rfl⟩; exact (hmemT x).mp hx)
  haveI : Fintype ↥T := hTfin.fintype
  let e : ↥(Tᶜ) ≃ {v : HeightOneSpectrum (𝓞 F) // v ∉ S} :=
    { toFun := fun x => ⟨x.1.1, (hmemc x.1).mp x.2⟩
      invFun := fun v => ⟨⟨v.1, fun h => v.2 (hST h)⟩, (hmemc _).mpr v.2⟩
      left_inv := fun x => rfl
      right_inv := fun v => rfl }
  have hcompl : Multipliable ((fun x : {v : HeightOneSpectrum (𝓞 F) // v ∉ ST} => f x.1) ∘ ((↑) : ↥(Tᶜ) → _)) :=
    (Equiv.multipliable_iff e).mpr hS
  have hfin : Multipliable ((fun x : {v : HeightOneSpectrum (𝓞 F) // v ∉ ST} => f x.1) ∘ ((↑) : ↥T → _)) :=
    Multipliable.of_finite
  have hsplit := T1E_aux T (fun x : {v : HeightOneSpectrum (𝓞 F) // v ∉ ST} => f x.1) hfin hcompl
  have h1 : (∏' x : ↥T, f x.1.1) = ∏ v ∈ S \ ST, f v := by
    rw [tprod_fintype]
    refine Finset.prod_nbij (fun x => x.1.1) (fun x _ => ?_) (fun x _ y _ h => ?_) (fun v hv => ?_) (fun x _ => rfl)
    · exact Finset.mem_sdiff.mpr ⟨(hmemT x.1).mp x.2, x.1.2⟩
    · exact Subtype.ext (Subtype.ext h)
    · obtain ⟨hvS, hvST⟩ := Finset.mem_sdiff.mp (Finset.mem_coe.mp hv)
      exact ⟨⟨⟨v, hvST⟩, (hmemT _).mpr hvS⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
  have h2 : (∏' x : ↥(Tᶜ), f x.1.1) = ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, f v.1 :=
    Equiv.tprod_eq e (fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => f v.1)
  rw [← h1, ← h2, ← hsplit]

end EulerSetChange

open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (S₁ S₂ : Finset (HeightOneSpectrum (𝓞 F))) (_h : S₁ ⊆ S₂)
    (z : HeightOneSpectrum (𝓞 F) → ℂ) (_hz : ∀ v, ‖z v‖ ≤ 1) (s : ℂ) (_hs : 1 < s.re) :
    (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₂},
        (1 - z v.1 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      * (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₁},
          (1 - z v.1 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))
      = ∏ v ∈ S₂ \ S₁, (1 - z v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) := by
  set f : HeightOneSpectrum (𝓞 F) → ℂ := fun v => 1 - z v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) with hf
  obtain ⟨hmul, htprod, hne⟩ := EulerSetChange.multipliable_and_tprod_eq_and_ne_zero S₂ z _hz s _hs
  have hsplit : (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₁}, f v.1)
      = (∏ v ∈ S₂ \ S₁, f v) * ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₂}, f v.1 :=
    EulerSetChange.T1E_tprod_split S₁ S₂ _h f hmul
  have hinv : (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₂}, (f v.1)⁻¹)
      * (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₂}, f v.1) = 1 := by
    have h2 : (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₂}, (f v.1)⁻¹) ≠ 0 := hne
    rw [show (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₂}, f v.1)
        = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₂}, (f v.1)⁻¹)⁻¹ from htprod, mul_inv_cancel₀ h2]
  show (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₂}, (f v.1)⁻¹)
      * (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S₁}, f v.1) = ∏ v ∈ S₂ \ S₁, f v
  rw [hsplit, mul_left_comm, hinv, mul_one]

end S_NumberField_tprod_inv_eulerFactor_mul_tprod_eulerFactor_eq_prod_sdiff_of_norm_le_one
end P2MW
export P2MW.S_NumberField_tprod_inv_eulerFactor_mul_tprod_eulerFactor_eq_prod_sdiff_of_norm_le_one (solution)
