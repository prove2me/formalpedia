-- Prove2me | solution 1 for ModularCurve.periodMap_heckeTLin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8f752da8-449b-5b66-aabf-0ad817605f0e

import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularForm_HeckeOperatorForms
import Theorems.Thm_ModularCurve_Period_CuspForm_exists_equivariantPrimitive_gamma0
import Theorems.Thm_ModularCurve_periodMap_eq_periodHom
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Module.Hom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_periodMap_heckeTLin

set_option Elab.async false
set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ModularCurve
p2m_export "ModularCurve" "periodMap Period.IsEquivariantPrimitive Period.CuspForm.exists_equivariantPrimitive_gamma0 periodMap_eq_periodHom"
namespace Period
p2m_export "ModularCurve.Period" "IsEquivariantPrimitive CuspForm.exists_equivariantPrimitive_gamma0"
namespace IsEquivariantPrimitive
p2m_export "ModularCurve.Period.IsEquivariantPrimitive" "period sub_eq_period periodHom"
p2m_open "ModularCurve.Period.IsEquivariantPrimitive ModularCurve.Period ModularCurve"

open UpperHalfPlane

variable {Γ : Subgroup SL(2, ℤ)} {F : ℍ → ℂ}

private theorem _root_.ModularCurve.Period.IsEquivariantPrimitive.period_congr {F' : ℍ → ℂ} (hF : IsEquivariantPrimitive Γ F)
    (hF' : IsEquivariantPrimitive Γ F') (c : ℂ) (h : ∀ z, F z - F' z = c) (γ : Γ) :
    hF.period γ = hF'.period γ := by
  rw [← hF.sub_eq_period γ UpperHalfPlane.I, ← hF'.sub_eq_period γ UpperHalfPlane.I]
  have h1 := h ((γ : SL(2, ℤ)) • UpperHalfPlane.I)
  have h2 := h UpperHalfPlane.I
  linear_combination h1 - h2

p2m_export "ModularCurve.Period.IsEquivariantPrimitive" "period_congr"
end ModularCurve.Period.IsEquivariantPrimitive

namespace ModularCurve
p2m_export "ModularCurve" "periodMap Period.IsEquivariantPrimitive Period.CuspForm.exists_equivariantPrimitive_gamma0 periodMap_eq_periodHom"
namespace Period
p2m_export "ModularCurve.Period" "IsEquivariantPrimitive CuspForm.exists_equivariantPrimitive_gamma0"
namespace SolHeckeT
p2m_open "ModularCurve.Period ModularCurve"

open UpperHalfPlane Filter Topology Complex

section Constancy

theorem apply_eq_apply_of_hasDerivAt_zero {D : ℂ → ℂ}
    (hD : ∀ τ : ℍ, HasDerivAt D 0 ↑τ) (z w : ℍ) : D ↑z = D ↑w := by
  have hmem : ∀ σ : ℍ, (↑σ : ℂ) ∈ {c : ℂ | 0 < c.im} := fun σ => σ.2
  refine isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero
    ((convex_halfSpace_im_gt 0).isPreconnected)
    (fun x hx => ((hD ⟨x, hx⟩).differentiableAt).differentiableWithinAt)
    (fun x hx => ?_) (hmem z) (hmem w)
  have h0 := ((hD ⟨x, hx⟩).hasFDerivAt).fderiv
  rw [Pi.zero_apply, h0]
  ext1
  simp

theorem sub_eq_const_of_forall_hasDerivAt {F G : ℂ → ℂ} {f : ℍ → ℂ}
    (hF : ∀ τ : ℍ, HasDerivAt F (f τ) ↑τ) (hG : ∀ τ : ℍ, HasDerivAt G (f τ) ↑τ) :
    ∃ c : ℂ, ∀ τ : ℍ, F ↑τ - G ↑τ = c := by
  refine ⟨F ↑UpperHalfPlane.I - G ↑UpperHalfPlane.I, fun τ => ?_⟩
  exact apply_eq_apply_of_hasDerivAt_zero
    (D := fun z => F z - G z) (fun σ => by have h__af := (hF σ).sub (hG σ); simp at h__af; exact h__af) τ UpperHalfPlane.I

end Constancy

namespace HeckeAnalytic

open Matrix CongruenceSubgroup

def repMat (ℓ : ℕ) : Option (Fin ℓ) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(ℓ : ℤ), 0; 0, 1]
  | some j => !![1, (j : ℤ); 0, (ℓ : ℤ)]

@[scoped simp] lemma repMat_none (ℓ : ℕ) : repMat ℓ none = !![(ℓ : ℤ), 0; 0, 1] := rfl

@[scoped simp] lemma repMat_some (ℓ : ℕ) (j : Fin ℓ) : repMat ℓ (some j) = !![1, (j : ℤ); 0, (ℓ : ℤ)] :=
  rfl

lemma det_repMat (ℓ : ℕ) (i : Option (Fin ℓ)) : (repMat ℓ i).det = (ℓ : ℤ) := by
  cases i <;> simp [repMat, Matrix.det_fin_two_of]

lemma exists_cocycle {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) {g : SL(2, ℤ)}
    (hg : g ∈ Gamma0 N) (i : Option (Fin ℓ)) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 N ∧ ∃ m : Option (Fin ℓ),
      repMat ℓ i * (g : Matrix (Fin 2) (Fin 2) ℤ)
        = (δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ m := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero

  have hdetG : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  have hNc : (N : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hg
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set a : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set d : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  have hgmat : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
    rw [ha, hb, hc, hd]; exact Matrix.eta_fin_two _

  have key : ∀ p t : ℤ, ¬ (ℓ : ℤ) ∣ p → ∃ j' : Fin ℓ, (ℓ : ℤ) ∣ t - p * (j' : ℤ) := by
    intro p t hp
    have hℓpos : (0 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.pos

    have hcop : IsCoprime (ℓ : ℤ) p :=
      (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hℓ)).mpr hp
    obtain ⟨u, v, huv⟩ := hcop
    have hmod := Int.emod_add_mul_ediv (v * t) (ℓ : ℤ)
    have hnonneg : 0 ≤ (v * t) % (ℓ : ℤ) := Int.emod_nonneg _ hℓ0
    have hlt : (v * t) % (ℓ : ℤ) < (ℓ : ℤ) := Int.emod_lt_of_pos _ hℓpos
    have hcoe : ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ) = (v * t) % (ℓ : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    refine ⟨⟨((v * t) % (ℓ : ℤ)).toNat, by omega⟩,
      ⟨t * u + p * ((v * t) / (ℓ : ℤ)), ?_⟩⟩
    show t - p * ((((v * t) % (ℓ : ℤ)).toNat : ℕ) : ℤ)
      = (ℓ : ℤ) * (t * u + p * ((v * t) / (ℓ : ℤ)))
    rw [hcoe]
    linear_combination (-t) * huv + (-p) * hmod
  cases i with
  | none =>

    by_cases hcdvd : (ℓ : ℤ) ∣ c
    ·
      obtain ⟨c', hc'⟩ := hcdvd
      have hdetδ : Matrix.det !![a, (ℓ : ℤ) * b; c', d] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG + b * hc'
      refine ⟨⟨_, hdetδ⟩, ?_, none, ?_⟩
      ·
        rw [Gamma0_mem]
        show ((c' : ℤ) : ZMod N) = 0
        have hcopN : Nat.Coprime N ℓ := ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN).symm
        have hcop : IsCoprime (N : ℤ) (ℓ : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr (by
          simpa [Int.gcd_natCast_natCast] using hcopN)
        have hNc' : (N : ℤ) ∣ c' := by
          refine hcop.dvd_of_dvd_mul_left ?_
          rw [← hc']
          exact hNc
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ none * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![a, (ℓ : ℤ) * b; c', d] * repMat ℓ none
        rw [hgmat, repMat_none, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show ((ℓ : ℤ) * a + 0 * c : ℤ) = a * (ℓ : ℤ) + (ℓ : ℤ) * b * 0
          ring
        · show ((ℓ : ℤ) * b + 0 * d : ℤ) = a * 0 + (ℓ : ℤ) * b * 1
          ring
        · show (0 * a + 1 * c : ℤ) = c' * (ℓ : ℤ) + d * 0
          linear_combination hc'
        · show (0 * b + 1 * d : ℤ) = c' * 0 + d * 1
          ring
    ·
      obtain ⟨j', hj'⟩ := key c d hcdvd
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det !![(ℓ : ℤ) * a, b - a * (j' : ℤ); c, e] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG - a * he
      refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_⟩
      · rw [Gamma0_mem]
        show ((c : ℤ) : ZMod N) = 0
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ none * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![(ℓ : ℤ) * a, b - a * (j' : ℤ); c, e] * repMat ℓ (some j')
        rw [hgmat, repMat_none, repMat_some, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show ((ℓ : ℤ) * a + 0 * c : ℤ) = (ℓ : ℤ) * a * 1 + (b - a * (j' : ℤ)) * 0
          ring
        · show ((ℓ : ℤ) * b + 0 * d : ℤ) = (ℓ : ℤ) * a * (j' : ℤ) + (b - a * (j' : ℤ)) * (ℓ : ℤ)
          ring
        · show (0 * a + 1 * c : ℤ) = c * 1 + e * 0
          ring
        · show (0 * b + 1 * d : ℤ) = c * (j' : ℤ) + e * (ℓ : ℤ)
          linear_combination he
  | some j =>

    by_cases hpdvd : (ℓ : ℤ) ∣ (a + (j : ℤ) * c)
    ·
      obtain ⟨p', hp'⟩ := hpdvd
      have hdetδ : Matrix.det !![p', b + (j : ℤ) * d; c, (ℓ : ℤ) * d] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG - d * hp'
      refine ⟨⟨_, hdetδ⟩, ?_, none, ?_⟩
      · rw [Gamma0_mem]
        show ((c : ℤ) : ZMod N) = 0
        rwa [ZMod.intCast_zmod_eq_zero_iff_dvd]
      · show repMat ℓ (some j) * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![p', b + (j : ℤ) * d; c, (ℓ : ℤ) * d] * repMat ℓ none
        rw [hgmat, repMat_some, repMat_none, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (1 * a + (j : ℤ) * c : ℤ) = p' * (ℓ : ℤ) + (b + (j : ℤ) * d) * 0
          linear_combination hp'
        · show (1 * b + (j : ℤ) * d : ℤ) = p' * 0 + (b + (j : ℤ) * d) * 1
          ring
        · show (0 * a + (ℓ : ℤ) * c : ℤ) = c * (ℓ : ℤ) + (ℓ : ℤ) * d * 0
          ring
        · show (0 * b + (ℓ : ℤ) * d : ℤ) = c * 0 + (ℓ : ℤ) * d * 1
          ring
    ·
      obtain ⟨j', hj'⟩ := key (a + (j : ℤ) * c) (b + (j : ℤ) * d) hpdvd
      obtain ⟨e, he⟩ := hj'
      have hdetδ : Matrix.det
          !![a + (j : ℤ) * c, e; (ℓ : ℤ) * c, d - c * (j' : ℤ)] = 1 := by
        rw [Matrix.det_fin_two_of]
        linear_combination hdetG + c * he
      refine ⟨⟨_, hdetδ⟩, ?_, some j', ?_⟩
      · rw [Gamma0_mem]
        show (((ℓ : ℤ) * c : ℤ) : ZMod N) = 0
        push_cast
        rw [show ((c : ℤ) : ZMod N) = 0 from (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNc,
          mul_zero]
      · show repMat ℓ (some j) * (g : Matrix (Fin 2) (Fin 2) ℤ)
          = !![a + (j : ℤ) * c, e; (ℓ : ℤ) * c, d - c * (j' : ℤ)] * repMat ℓ (some j')
        rw [hgmat, repMat_some, repMat_some, Matrix.mul_fin_two, Matrix.mul_fin_two]
        refine Matrix.ext fun x y => ?_
        fin_cases x <;> fin_cases y
        · show (1 * a + (j : ℤ) * c : ℤ) = (a + (j : ℤ) * c) * 1 + e * 0
          ring
        · show (1 * b + (j : ℤ) * d : ℤ) = (a + (j : ℤ) * c) * (j' : ℤ) + e * (ℓ : ℤ)
          linear_combination he
        · show (0 * a + (ℓ : ℤ) * c : ℤ) = (ℓ : ℤ) * c * 1 + (d - c * (j' : ℤ)) * 0
          ring
        · show (0 * b + (ℓ : ℤ) * d : ℤ) = (ℓ : ℤ) * c * (j' : ℤ) + (d - c * (j' : ℤ)) * (ℓ : ℤ)
          ring

def repGL (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repMat ℓ i).map (algebraMap ℤ ℝ)) (by
    have h : ((repMat ℓ i).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) (repMat ℓ i).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, det_repMat]
    simp [NeZero.ne ℓ])

@[scoped simp] lemma repGL_coe (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) :
    (repGL ℓ i : Matrix (Fin 2) (Fin 2) ℝ) = (repMat ℓ i).map (algebraMap ℤ ℝ) := rfl

private lemma mapGL_coe' (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

private lemma map_int_mul (M P : Matrix (Fin 2) (Fin 2) ℤ) :
    (M * P).map (algebraMap ℤ ℝ) = M.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

def heckeSlashSum (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ i

section BoardBridge

variable (ℓ : ℕ) [NeZero ℓ]

theorem repGL_some_eq_heckeMatrix (j : Fin ℓ) :
    repGL ℓ (some j) = ModularForm.heckeMatrix ℓ j := by
  refine Units.ext ?_
  rw [repGL_coe, ModularForm.val_heckeMatrix (NeZero.ne ℓ), repMat_some]
  ext i k
  fin_cases i <;> fin_cases k <;> simp

theorem repGL_none_eq_heckeDiagMatrix :
    repGL ℓ none = ModularForm.heckeDiagMatrix ℓ := by
  refine Units.ext ?_
  rw [repGL_coe, ModularForm.val_heckeDiagMatrix (NeZero.ne ℓ), repMat_none]
  ext i k
  fin_cases i <;> fin_cases k <;> simp

theorem heckeSlashSum_eq_heckeT (k : ℤ) (f : UpperHalfPlane → ℂ) :
    heckeSlashSum k ℓ f = ModularForm.heckeT k ℓ f := by
  rw [heckeSlashSum, ModularForm.heckeT_def, Fintype.sum_option, repGL_none_eq_heckeDiagMatrix,
    add_comm, ← Fin.sum_univ_eq_sum_range (fun j => f ∣[k] ModularForm.heckeMatrix ℓ j) ℓ]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [repGL_some_eq_heckeMatrix]

end BoardBridge

end HeckeAnalytic
p2m_reactivate "P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic"

open UpperHalfPlane Filter Topology Complex Function ModularForm Matrix CongruenceSubgroup Subgroup HeckeEis

section ChainRule

theorem slash_two_apply_of_det_pos (f : ℍ → ℂ) {β : GL (Fin 2) ℝ} (hβ : 0 < β.val.det)
    (τ : ℍ) :
    (f ∣[(2 : ℤ)] β) τ = f (β • τ) * (↑β.val.det / denom β ↑τ ^ 2) := by
  have hβ' : 0 < β.det.val := by
    rwa [Matrix.GeneralLinearGroup.val_det_apply]
  rw [ModularForm.slash_apply, σ, if_pos hβ', ContinuousAlgEquiv.refl_apply]
  have habs : |β.det.val| = β.val.det := by
    rw [abs_of_pos hβ', Matrix.GeneralLinearGroup.val_det_apply]
  rw [habs, show (2 : ℤ) - 1 = 1 by norm_num, zpow_one, _root_.zpow_neg, zpow_ofNat, mul_assoc,
    ← div_eq_mul_inv]

theorem hasDerivAt_comp_smul_of_det_pos {G : ℍ → ℂ} {g : ℍ → ℂ}
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) {β : GL (Fin 2) ℝ}
    (hβ : 0 < β.val.det) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => G (β • ofComplex z)) ((g ∣[(2 : ℤ)] β) τ) ↑τ := by
  have hfun : (fun z : ℂ => G (β • ofComplex z))
      = (G ∘ ofComplex) ∘ fun z : ℂ => ((β • ofComplex z : ℍ) : ℂ) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]
  have houter : HasDerivAt (G ∘ ofComplex) (g (β • τ))
      ((fun z : ℂ => ((β • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hG (β • τ)
  have hinner : HasDerivAt (fun z : ℂ => ((β • ofComplex z : ℍ) : ℂ))
      (↑β.val.det / denom β ↑τ ^ 2) ↑τ :=
    (UpperHalfPlane.hasStrictDerivAt_smul hβ τ).hasDerivAt
  have hcomp := houter.comp (↑τ : ℂ) hinner
  rw [← hfun] at hcomp
  rw [slash_two_apply_of_det_pos g hβ τ]
  exact hcomp

end ChainRule
p2m_reactivate "P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic"

noncomputable local instance (N ℓ : ℕ) [NeZero ℓ] :
    Fintype (Gamma0 N ⧸ heckeUpper N ℓ) :=
  (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex

section CosetRep

variable (N ℓ : ℕ) [NeZero ℓ]

private theorem map_int_mul' (M P : Matrix (Fin 2) (Fin 2) ℤ) :
    (M * P).map (algebraMap ℤ ℝ) = M.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

noncomputable def alphaGL : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((alphaMat ℓ).map (algebraMap ℤ ℝ)) (by
    have h : ((alphaMat ℓ).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) (alphaMat ℓ).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, det_alphaMat]
    simp [NeZero.ne ℓ])

@[scoped simp]
theorem alphaGL_coe :
    (alphaGL ℓ : Matrix (Fin 2) (Fin 2) ℝ) = (alphaMat ℓ).map (algebraMap ℤ ℝ) :=
  rfl

theorem alphaGL_val_det : (alphaGL ℓ).val.det = (ℓ : ℝ) := by
  show ((alphaMat ℓ).map (algebraMap ℤ ℝ)).det = (ℓ : ℝ)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, det_alphaMat]
  simp

noncomputable def gammaToGL : Gamma0 N →* GL (Fin 2) ℝ :=
  (Matrix.SpecialLinearGroup.mapGL ℝ).comp (Gamma0 N).subtype

@[scoped simp]
theorem gammaToGL_apply (x : Gamma0 N) :
    gammaToGL N x = Matrix.SpecialLinearGroup.mapGL ℝ (x : SL(2, ℤ)) :=
  rfl

theorem gammaToGL_val_det (x : Gamma0 N) : (gammaToGL N x).val.det = 1 := by
  rw [gammaToGL_apply, ← Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.SpecialLinearGroup.det_mapGL, Units.val_one]

theorem gammaToGL_smul (x : Gamma0 N) (z : ℍ) : gammaToGL N x • z = (x : SL(2, ℤ)) • z :=
  rfl

noncomputable def heckeCosetRep (q : Gamma0 N ⧸ heckeUpper N ℓ) : GL (Fin 2) ℝ :=
  alphaGL ℓ * gammaToGL N (Quotient.out q)⁻¹

theorem heckeCosetRep_def (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    heckeCosetRep N ℓ q = alphaGL ℓ * gammaToGL N (Quotient.out q)⁻¹ :=
  rfl

theorem heckeCosetRep_val_det (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    (heckeCosetRep N ℓ q).val.det = (ℓ : ℝ) := by
  rw [heckeCosetRep_def, Units.val_mul, Matrix.det_mul, alphaGL_val_det, gammaToGL_val_det,
    mul_one]

theorem heckeCosetRep_val_det_pos (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    0 < (heckeCosetRep N ℓ q).val.det := by
  rw [heckeCosetRep_val_det]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)

theorem gammaToGL_heckeConj_mul_alphaGL (h : heckeUpper N ℓ) :
    gammaToGL N (heckeConj N ℓ h) * alphaGL ℓ = alphaGL ℓ * gammaToGL N (h : Gamma0 N) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (heckeConjMat ℓ ((((h : Gamma0 N) : SL(2, ℤ))) : Matrix (Fin 2) (Fin 2) ℤ)).map
        (algebraMap ℤ ℝ) * ((alphaMat ℓ).map (algebraMap ℤ ℝ))
      = ((alphaMat ℓ).map (algebraMap ℤ ℝ))
        * ((((h : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ))
  rw [← map_int_mul', ← map_int_mul',
    heckeConjMat_mul_alphaMat ((mem_heckeUpper N ℓ).mp h.2)]

omit [NeZero ℓ] in

theorem coe_transferAux_inv_smul (γ : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    ((transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q) : heckeUpper N ℓ) : Gamma0 N)
      = (Quotient.out q)⁻¹ * (γ * Quotient.out (γ⁻¹ • q)) := by
  rw [coe_transferAux, smul_inv_smul]

theorem heckeCosetRep_mul_gammaToGL (γ : Gamma0 N) (q : Gamma0 N ⧸ heckeUpper N ℓ) :
    heckeCosetRep N ℓ q * gammaToGL N γ
      = gammaToGL N (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q)))
        * heckeCosetRep N ℓ (γ⁻¹ • q) := by
  rw [heckeCosetRep_def, heckeCosetRep_def, ← mul_assoc, gammaToGL_heckeConj_mul_alphaGL,
    mul_assoc, mul_assoc, ← map_mul (gammaToGL N), ← map_mul (gammaToGL N)]
  refine congrArg (fun x : Gamma0 N => alphaGL ℓ * gammaToGL N x) ?_
  rw [coe_transferAux_inv_smul]
  group

end CosetRep
p2m_reactivate "P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic"

section Telescoping

variable {N ℓ : ℕ} [NeZero ℓ] {Fprim : ℍ → ℂ}

theorem sum_heckeCosetRep_smul_sub (hF : IsEquivariantPrimitive (Gamma0 N) Fprim)
    (γ : Gamma0 N) (z : ℍ) :
    ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
        (Fprim (heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z))
          - Fprim (heckeCosetRep N ℓ q • z))
      = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          hF.period (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)) := by

  have hterm : ∀ q : Gamma0 N ⧸ heckeUpper N ℓ,
      Fprim (heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z))
        = Fprim (heckeCosetRep N ℓ (γ⁻¹ • q) • z)
          + hF.period
              (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q))) := by
    intro q
    have h1 : heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z)
        = ((heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q)) : Gamma0 N)
            : SL(2, ℤ)) • (heckeCosetRep N ℓ (γ⁻¹ • q) • z) := by
      rw [show ((γ : SL(2, ℤ)) • z) = gammaToGL N γ • z from rfl, ← mul_smul,
        heckeCosetRep_mul_gammaToGL, mul_smul]
      rfl
    rw [h1]
    have h2 := hF.sub_eq_period
      (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q)))
      (heckeCosetRep N ℓ (γ⁻¹ • q) • z)
    linear_combination h2

  calc
    ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
        (Fprim (heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z))
          - Fprim (heckeCosetRep N ℓ q • z))
      = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          (Fprim (heckeCosetRep N ℓ (γ⁻¹ • q) • z)
            + hF.period
                (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q)))
            - Fprim (heckeCosetRep N ℓ q • z)) :=
        Finset.sum_congr rfl fun q _ => by rw [hterm q]
    _ = (∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ (γ⁻¹ • q) • z))
          + (∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
              hF.period
                (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ (γ⁻¹ • q))))
          - ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • z) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = (∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • z))
          + (∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
              hF.period (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)))
          - ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • z) := by
        rw [(MulAction.bijective (γ⁻¹ : Gamma0 N)).sum_comp
            (fun q : Gamma0 N ⧸ heckeUpper N ℓ => Fprim (heckeCosetRep N ℓ q • z)),
          (MulAction.bijective (γ⁻¹ : Gamma0 N)).sum_comp
            (fun q : Gamma0 N ⧸ heckeUpper N ℓ => hF.period
              (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)))]
    _ = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          hF.period (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)) := by
        ring

end Telescoping
p2m_reactivate "P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic"

section Main

variable {N ℓ : ℕ} [NeZero ℓ]

variable (N ℓ) in

noncomputable def heckeQuotSlashSum (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, f ∣[(2 : ℤ)] heckeCosetRep N ℓ q

theorem hasDerivAt_sum_heckeCosetRep {Fprim : ℍ → ℂ} {f : ℍ → ℂ}
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ) (τ : ℍ) :
    HasDerivAt
      ((fun w : ℍ => ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • w))
        ∘ ofComplex)
      (heckeQuotSlashSum N ℓ f τ) ↑τ := by
  have key := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Gamma0 N ⧸ heckeUpper N ℓ)))
    (x := (↑τ : ℂ))
    (A := fun (q : Gamma0 N ⧸ heckeUpper N ℓ) (z : ℂ) =>
      Fprim (heckeCosetRep N ℓ q • ofComplex z))
    (A' := fun q : Gamma0 N ⧸ heckeUpper N ℓ => (f ∣[(2 : ℤ)] heckeCosetRep N ℓ q) τ)
    (fun q _ => hasDerivAt_comp_smul_of_det_pos hFf (heckeCosetRep_val_det_pos N ℓ q) τ)
  rw [show heckeQuotSlashSum N ℓ f τ
      = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, (f ∣[(2 : ℤ)] heckeCosetRep N ℓ q) τ from
    Finset.sum_apply τ Finset.univ fun q => f ∣[(2 : ℤ)] heckeCosetRep N ℓ q]
  exact key

theorem periodHom_heckeQuotSlashSum {Fprim Fprim' : ℍ → ℂ} {f : ℍ → ℂ}
    (hF : IsEquivariantPrimitive (Gamma0 N) Fprim)
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ)
    (hF' : IsEquivariantPrimitive (Gamma0 N) Fprim')
    (hF'f : ∀ τ : ℍ, HasDerivAt (Fprim' ∘ ofComplex) (heckeQuotSlashSum N ℓ f τ) ↑τ) :
    hF'.periodHom = heckeOperatorHom N ℓ ℂ hF.periodHom := by

  have hGsub : ∀ (γ : Gamma0 N) (z : ℍ),
      (∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          Fprim (heckeCosetRep N ℓ q • ((γ : SL(2, ℤ)) • z)))
        - (∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • z))
        = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
            hF.period (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)) := by
    intro γ z
    rw [← Finset.sum_sub_distrib]
    exact sum_heckeCosetRep_smul_sub hF γ z

  have hGequiv : IsEquivariantPrimitive (Gamma0 N)
      (fun w : ℍ => ∑ q : Gamma0 N ⧸ heckeUpper N ℓ, Fprim (heckeCosetRep N ℓ q • w)) :=
    fun γ =>
      ⟨∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
          hF.period (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)),
        fun z => hGsub γ z⟩

  have hGperiod : ∀ γ : Gamma0 N,
      hGequiv.period γ
        = ∑ q : Gamma0 N ⧸ heckeUpper N ℓ,
            hF.period (heckeConj N ℓ (transferAux (heckeUpper N ℓ) γ q)) := by
    intro γ
    rw [← hGequiv.sub_eq_period γ UpperHalfPlane.I]
    exact hGsub γ UpperHalfPlane.I

  obtain ⟨c, hc⟩ := sub_eq_const_of_forall_hasDerivAt hF'f (hasDerivAt_sum_heckeCosetRep hFf)
  refine AddMonoidHom.ext fun x => ?_
  show hF'.period (Additive.toMul x)
    = heckeOperatorHom N ℓ ℂ hF.periodHom (Additive.ofMul (Additive.toMul x))
  rw [hF'.period_congr hGequiv c (fun w => by
      simpa only [Function.comp_apply, ofComplex_apply] using hc w) (Additive.toMul x),
    hGperiod (Additive.toMul x), heckeOperatorHom_apply]
  rfl

end Main
p2m_reactivate "P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic"

section Bridge

variable {N : ℕ} [NeZero N] {ℓ : ℕ} [NeZero ℓ]

variable (N ℓ) in

def HeckeCosetMatch : Prop :=
  ∃ e : Option (Fin ℓ) ≃ (Gamma0 N ⧸ heckeUpper N ℓ),
    ∀ i : Option (Fin ℓ), ∃ δ : Gamma0 N,
      HeckeAnalytic.repGL ℓ i = gammaToGL N δ * heckeCosetRep N ℓ (e i)

omit [NeZero N] in

theorem heckeSlashSum_eq_heckeQuotSlashSum (hmatch : HeckeCosetMatch N ℓ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[(2 : ℤ)] γ = f) :
    HeckeAnalytic.heckeSlashSum 2 ℓ f = heckeQuotSlashSum N ℓ f := by
  obtain ⟨e, he⟩ := hmatch
  rw [HeckeAnalytic.heckeSlashSum, heckeQuotSlashSum,
    ← Equiv.sum_comp e fun q => f ∣[(2 : ℤ)] heckeCosetRep N ℓ q]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨δ, hδ⟩ := he i
  rw [hδ, SlashAction.slash_mul,
    hf (gammaToGL N δ) (Subgroup.mem_map.mpr ⟨(δ : SL(2, ℤ)), δ.2, rfl⟩)]

omit [NeZero N] in

theorem periodHom_heckeSlashSum_of_match (hmatch : HeckeCosetMatch N ℓ)
    (f : CuspForm (Gamma0 N) 2) {Fprim Fprim' : ℍ → ℂ}
    (hF : IsEquivariantPrimitive (Gamma0 N) Fprim)
    (hFf : ∀ τ : ℍ, HasDerivAt (Fprim ∘ ofComplex) (f τ) ↑τ)
    (hF' : IsEquivariantPrimitive (Gamma0 N) Fprim')
    (hF'f : ∀ τ : ℍ, HasDerivAt (Fprim' ∘ ofComplex) (HeckeAnalytic.heckeSlashSum 2 ℓ (⇑f) τ) ↑τ) :
    hF'.periodHom = heckeOperatorHom N ℓ ℂ hF.periodHom := by
  refine periodHom_heckeQuotSlashSum hF hFf hF' fun τ => ?_
  rw [← heckeSlashSum_eq_heckeQuotSlashSum hmatch (SlashInvariantFormClass.slash_action_eq f)]
  exact hF'f τ

end Bridge
p2m_reactivate "P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic"

open HeckeAnalytic

section Representatives

def unipotentUpper (N : ℕ) (t : ℤ) : Gamma0 N :=
  ⟨⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩, by
    rw [Gamma0_mem]
    show ((0 : ℤ) : ZMod N) = 0
    exact Int.cast_zero⟩

theorem unipotentUpper_mul (N : ℕ) (s t : ℤ) :
    unipotentUpper N s * unipotentUpper N t = unipotentUpper N (s + t) := by
  refine Subtype.ext (Subtype.ext ?_)
  show (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1, t; 0, 1] = !![1, s + t; 0, 1]
  rw [Matrix.mul_fin_two]
  refine Matrix.ext fun x y => ?_
  fin_cases x <;> fin_cases y
  · show (1 * 1 + s * 0 : ℤ) = 1
    ring
  · show (1 * t + s * 1 : ℤ) = s + t
    ring
  · show (0 * 1 + 1 * 0 : ℤ) = 0
    ring
  · show (0 * t + 1 * 1 : ℤ) = 1
    ring

theorem unipotentUpper_zero (N : ℕ) : unipotentUpper N 0 = 1 := by
  refine Subtype.ext (Subtype.ext ?_)
  show (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) = 1
  rw [Matrix.one_fin_two]

theorem inv_unipotentUpper (N : ℕ) (t : ℤ) :
    (unipotentUpper N t)⁻¹ = unipotentUpper N (-t) :=
  inv_eq_of_mul_eq_one_right (by
    rw [unipotentUpper_mul, show t + -t = 0 by ring, unipotentUpper_zero])

variable {N ℓ : ℕ}

theorem hecke_bezout (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    (ℓ : ℤ) * Nat.gcdA ℓ N + (N : ℤ) * Nat.gcdB ℓ N = 1 := by
  have h := Nat.gcd_eq_gcd_ab ℓ N
  rw [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN)] at h
  exact_mod_cast h.symm

theorem not_dvd_gcdB (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : ¬ (ℓ : ℤ) ∣ Nat.gcdB ℓ N := by
  intro hdvd
  have h1 : (ℓ : ℤ) ∣ 1 := by
    rw [← hecke_bezout hℓ hℓN]
    exact dvd_add (dvd_mul_right _ _) (hdvd.mul_left _)
  have h2 : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
  have h3 : (1 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ.one_lt
  omega

def bezoutRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : Gamma0 N :=
  ⟨⟨!![Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), (ℓ : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linear_combination hecke_bezout hℓ hℓN⟩, by
    rw [Gamma0_mem]
    show ((N : ℤ) : ZMod N) = 0
    rw [Int.cast_natCast]
    exact ZMod.natCast_self N⟩

def cosetRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : Option (Fin ℓ) → Gamma0 N
  | none => bezoutRep hℓ hℓN
  | some j => unipotentUpper N (-(j : ℤ))

@[scoped simp]
theorem cosetRep_none (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    cosetRep hℓ hℓN (none : Option (Fin ℓ)) = bezoutRep hℓ hℓN :=
  rfl

@[scoped simp]
theorem cosetRep_some (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (j : Fin ℓ) :
    cosetRep hℓ hℓN (some j) = unipotentUpper N (-(j : ℤ)) :=
  rfl

def rawDelta (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : Option (Fin ℓ) → Gamma0 N
  | none =>
    ⟨⟨!![(ℓ : ℤ) * Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), 1], by
      rw [Matrix.det_fin_two_of]
      linear_combination hecke_bezout hℓ hℓN⟩, by
      rw [Gamma0_mem]
      show ((N : ℤ) : ZMod N) = 0
      rw [Int.cast_natCast]
      exact ZMod.natCast_self N⟩
  | some _ => 1

theorem repMat_mul_cosetRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    repMat ℓ i * (((cosetRep hℓ hℓN i : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (((rawDelta hℓ hℓN i : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
          * alphaMat ℓ := by
  match i with
  | none =>
    show !![(ℓ : ℤ), 0; 0, 1] * !![Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), (ℓ : ℤ)]
        = !![(ℓ : ℤ) * Nat.gcdA ℓ N, -Nat.gcdB ℓ N; (N : ℤ), 1] * !![1, 0; 0, (ℓ : ℤ)]
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun x y => ?_
    fin_cases x <;> fin_cases y
    · show ((ℓ : ℤ) * Nat.gcdA ℓ N + 0 * (N : ℤ) : ℤ)
        = (ℓ : ℤ) * Nat.gcdA ℓ N * 1 + -Nat.gcdB ℓ N * 0
      ring
    · show ((ℓ : ℤ) * -Nat.gcdB ℓ N + 0 * (ℓ : ℤ) : ℤ)
        = (ℓ : ℤ) * Nat.gcdA ℓ N * 0 + -Nat.gcdB ℓ N * (ℓ : ℤ)
      ring
    · show (0 * Nat.gcdA ℓ N + 1 * (N : ℤ) : ℤ) = (N : ℤ) * 1 + 1 * 0
      ring
    · show (0 * -Nat.gcdB ℓ N + 1 * (ℓ : ℤ) : ℤ) = (N : ℤ) * 0 + 1 * (ℓ : ℤ)
      ring
  | some j =>
    show !![1, (j : ℤ); 0, (ℓ : ℤ)] * !![1, -(j : ℤ); 0, 1]
        = (1 : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, (ℓ : ℤ)]
    rw [Matrix.mul_fin_two, Matrix.one_mul]
    refine Matrix.ext fun x y => ?_
    fin_cases x <;> fin_cases y
    · show (1 * 1 + (j : ℤ) * 0 : ℤ) = 1
      ring
    · show (1 * -(j : ℤ) + (j : ℤ) * 1 : ℤ) = 0
      ring
    · show (0 * 1 + (ℓ : ℤ) * 0 : ℤ) = 0
      ring
    · show (0 * -(j : ℤ) + (ℓ : ℤ) * 1 : ℤ) = (ℓ : ℤ)
      ring

end Representatives
p2m_reactivate "P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic"

section Bijection

variable {N ℓ : ℕ}

def cosetOfRep (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    Gamma0 N ⧸ heckeUpper N ℓ :=
  (cosetRep hℓ hℓN i : Gamma0 N ⧸ heckeUpper N ℓ)

theorem cosetOfRep_def (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    cosetOfRep hℓ hℓN i = (cosetRep hℓ hℓN i : Gamma0 N ⧸ heckeUpper N ℓ) :=
  rfl

private theorem unipotentUpper_mul_mem_iff (s t : ℤ) :
    unipotentUpper N s * unipotentUpper N t ∈ heckeUpper N ℓ ↔ (ℓ : ℤ) ∣ (s + t) := by
  rw [unipotentUpper_mul, mem_heckeUpper]
  exact Iff.rfl

private theorem unipotentUpper_mul_bezoutRep_not_mem (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (s : ℤ) :
    unipotentUpper N s * bezoutRep hℓ hℓN ∉ heckeUpper N ℓ := by
  intro hmem
  rw [mem_heckeUpper] at hmem

  have hentry : (((unipotentUpper N s * bezoutRep hℓ hℓN : Gamma0 N) : SL(2, ℤ))) 0 1
      = 1 * -Nat.gcdB ℓ N + s * (ℓ : ℤ) :=
    (Matrix.two_mul_expl
      (((unipotentUpper N s : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      (((bezoutRep hℓ hℓN : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).2.1
  rw [hentry,
    show (1 : ℤ) * -Nat.gcdB ℓ N + s * (ℓ : ℤ) = s * (ℓ : ℤ) - Nat.gcdB ℓ N by ring] at hmem

  exact not_dvd_gcdB hℓ hℓN ((dvd_sub_right (dvd_mul_left _ _)).mp hmem)

theorem cosetOfRep_injective (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    Function.Injective (cosetOfRep (N := N) hℓ hℓN) := by
  intro i i' h
  rw [cosetOfRep_def, cosetOfRep_def, QuotientGroup.eq] at h
  match i, i' with
  | none, none => rfl
  | some j, none =>

    exact absurd h (by
      rw [cosetRep_some, cosetRep_none, inv_unipotentUpper, neg_neg]
      exact unipotentUpper_mul_bezoutRep_not_mem hℓ hℓN (j : ℤ))
  | none, some j' =>

    refine absurd ((heckeUpper N ℓ).inv_mem h) ?_
    rw [cosetRep_some, cosetRep_none, _root_.mul_inv_rev, inv_inv, inv_unipotentUpper, neg_neg]
    exact unipotentUpper_mul_bezoutRep_not_mem hℓ hℓN (j' : ℤ)
  | some j, some j' =>

    rw [cosetRep_some, cosetRep_some, inv_unipotentUpper, neg_neg,
      unipotentUpper_mul_mem_iff] at h

    have hj := j.isLt
    have hj' := j'.isLt
    have hzero : (j : ℤ) + -(j' : ℤ) = 0 := by
      refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_
      rw [Int.natAbs_natCast]
      omega
    have hval : (j : ℕ) = (j' : ℕ) := by omega
    exact congrArg some (Fin.ext hval)

private theorem dvd_of_alphaMat_mul_eq_mul_alphaMat {X Y : Matrix (Fin 2) (Fin 2) ℤ}
    (h : alphaMat ℓ * X = Y * alphaMat ℓ) : (ℓ : ℤ) ∣ X 0 1 := by
  have h01 : (alphaMat ℓ * X) 0 1 = (Y * alphaMat ℓ) 0 1 := by rw [h]
  rw [(Matrix.two_mul_expl (alphaMat ℓ) X).2.1, (Matrix.two_mul_expl Y (alphaMat ℓ)).2.1,
    alphaMat_apply_zero_zero, alphaMat_apply_zero_one, alphaMat_apply_one_one] at h01
  exact ⟨Y 0 1, by linear_combination h01⟩

private theorem repMat_some_zero (hpos : 0 < ℓ) : repMat ℓ (some ⟨0, hpos⟩) = alphaMat ℓ := by
  rw [repMat_some]
  rfl

theorem cosetOfRep_surjective (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    Function.Surjective (cosetOfRep (N := N) hℓ hℓN) := by
  intro q
  obtain ⟨γ, rfl⟩ : ∃ γ : Gamma0 N, (γ : Gamma0 N ⧸ heckeUpper N ℓ) = q :=
    ⟨Quotient.out q, QuotientGroup.out_eq' q⟩

  obtain ⟨δ, -, m, hm⟩ := exists_cocycle hℓ hℓN (γ⁻¹ : Gamma0 N).2 (some ⟨0, hℓ.pos⟩)
  refine ⟨m, ?_⟩
  rw [cosetOfRep_def, QuotientGroup.eq, ← (heckeUpper N ℓ).inv_mem_iff, _root_.mul_inv_rev,
    inv_inv, mem_heckeUpper]

  refine dvd_of_alphaMat_mul_eq_mul_alphaMat
    (Y := (δ : Matrix (Fin 2) (Fin 2) ℤ)
      * (((rawDelta hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) ?_
  have hcoe : (((γ⁻¹ * cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (((γ⁻¹ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) :=
    rfl
  calc alphaMat ℓ
      * (((γ⁻¹ * cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (alphaMat ℓ * (((γ⁻¹ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [hcoe, mul_assoc]
    _ = (repMat ℓ (some ⟨0, hℓ.pos⟩)
          * (((γ⁻¹ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [repMat_some_zero hℓ.pos]
    _ = ((δ : Matrix (Fin 2) (Fin 2) ℤ) * repMat ℓ m)
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
        rw [hm]
    _ = (δ : Matrix (Fin 2) (Fin 2) ℤ) * (repMat ℓ m
          * (((cosetRep hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
        rw [mul_assoc]
    _ = (δ : Matrix (Fin 2) (Fin 2) ℤ)
          * ((((rawDelta hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
            * alphaMat ℓ) := by
        rw [repMat_mul_cosetRep]
    _ = ((δ : Matrix (Fin 2) (Fin 2) ℤ)
          * (((rawDelta hℓ hℓN m : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
          * alphaMat ℓ := by
        rw [mul_assoc]

noncomputable def heckeCosetEquiv (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    Option (Fin ℓ) ≃ (Gamma0 N ⧸ heckeUpper N ℓ) :=
  Equiv.ofBijective (cosetOfRep hℓ hℓN)
    ⟨cosetOfRep_injective hℓ hℓN, cosetOfRep_surjective hℓ hℓN⟩

@[scoped simp]
theorem heckeCosetEquiv_apply (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    heckeCosetEquiv hℓ hℓN i = (cosetRep hℓ hℓN i : Gamma0 N ⧸ heckeUpper N ℓ) :=
  rfl

end Bijection
p2m_reactivate "P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic"

section CosetMatch

variable {N ℓ : ℕ} [NeZero ℓ]

private theorem map_int_mul'' (M P : Matrix (Fin 2) (Fin 2) ℤ) :
    (M * P).map (algebraMap ℤ ℝ) = M.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

theorem repGL_eq_rawDelta_mul (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Option (Fin ℓ)) :
    repGL ℓ i = gammaToGL N (rawDelta hℓ hℓN i)
      * (alphaGL ℓ * gammaToGL N (cosetRep hℓ hℓN i)⁻¹) := by
  have key : repGL ℓ i * gammaToGL N (cosetRep hℓ hℓN i)
      = gammaToGL N (rawDelta hℓ hℓN i) * alphaGL ℓ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (repMat ℓ i).map (algebraMap ℤ ℝ)
        * ((((cosetRep hℓ hℓN i : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
            (algebraMap ℤ ℝ))
      = ((((rawDelta hℓ hℓN i : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map
            (algebraMap ℤ ℝ))
        * ((alphaMat ℓ).map (algebraMap ℤ ℝ))
    rw [← map_int_mul'', ← map_int_mul'', repMat_mul_cosetRep]
  calc repGL ℓ i
      = (repGL ℓ i * gammaToGL N (cosetRep hℓ hℓN i))
          * (gammaToGL N (cosetRep hℓ hℓN i))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = (gammaToGL N (rawDelta hℓ hℓN i) * alphaGL ℓ)
          * (gammaToGL N (cosetRep hℓ hℓN i))⁻¹ := by
        rw [key]
    _ = gammaToGL N (rawDelta hℓ hℓN i)
          * (alphaGL ℓ * gammaToGL N (cosetRep hℓ hℓN i)⁻¹) := by
        rw [mul_assoc, map_inv]

theorem exists_heckeCosetRep_coe_eq (γ : Gamma0 N) :
    ∃ ε : Gamma0 N, heckeCosetRep N ℓ (γ : Gamma0 N ⧸ heckeUpper N ℓ)
      = gammaToGL N ε * (alphaGL ℓ * gammaToGL N γ⁻¹) := by
  obtain ⟨h, hout⟩ := QuotientGroup.mk_out_eq_mul (heckeUpper N ℓ) γ
  refine ⟨heckeConj N ℓ h⁻¹, ?_⟩
  rw [heckeCosetRep_def,
    show Quotient.out ((γ : Gamma0 N ⧸ heckeUpper N ℓ)) = γ * (h : Gamma0 N) from hout,
    _root_.mul_inv_rev, map_mul, ← mul_assoc, ← mul_assoc]
  congr 1

  exact (gammaToGL_heckeConj_mul_alphaGL N ℓ h⁻¹).symm

theorem heckeCosetMatch (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) : HeckeCosetMatch N ℓ := by
  refine ⟨heckeCosetEquiv hℓ hℓN, fun i => ?_⟩
  obtain ⟨ε, hε⟩ := exists_heckeCosetRep_coe_eq (ℓ := ℓ) (cosetRep hℓ hℓN i)
  refine ⟨rawDelta hℓ hℓN i * ε⁻¹, ?_⟩
  rw [show heckeCosetEquiv hℓ hℓN i = (cosetRep hℓ hℓN i : Gamma0 N ⧸ heckeUpper N ℓ) from rfl,
    hε, map_mul, map_inv, mul_assoc, ← mul_assoc ((gammaToGL N ε)⁻¹), inv_mul_cancel, one_mul]
  exact repGL_eq_rawDelta_mul hℓ hℓN i

end CosetMatch
p2m_reactivate "P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic"

end ModularCurve.Period.SolHeckeT
p2m_reactivate "P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT"
p2m_reactivate "P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period"
p2m_reactivate "P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT.HeckeAnalytic P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period P2MW.S_ModularCurve_periodMap_heckeTLin.ModularCurve.Period.SolHeckeT"

theorem solution {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ModularCurve.periodMap N (CuspForm.heckeTLin 2 hℓ hℓN f)
      = HeckeEis.heckeOperatorHom N ℓ ℂ (ModularCurve.periodMap N f) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : NeZero N := ⟨fun h => hℓN (h ▸ dvd_zero ℓ)⟩
  obtain ⟨F, hFf, -, hFe, -⟩ := ModularCurve.Period.CuspForm.exists_equivariantPrimitive_gamma0 f
  obtain ⟨F', hF'f, -, hF'e, -⟩ :=
    ModularCurve.Period.CuspForm.exists_equivariantPrimitive_gamma0 (CuspForm.heckeTLin 2 hℓ hℓN f)
  rw [ModularCurve.periodMap_eq_periodHom hF'e hF'f, ModularCurve.periodMap_eq_periodHom hFe hFf]
  refine ModularCurve.Period.SolHeckeT.periodHom_heckeSlashSum_of_match
    (ModularCurve.Period.SolHeckeT.heckeCosetMatch hℓ hℓN) f hFe hFf hF'e fun τ => ?_
  rw [ModularCurve.Period.SolHeckeT.HeckeAnalytic.heckeSlashSum_eq_heckeT ℓ 2 ⇑f,
    ← CuspForm.coe_heckeTLin_apply 2 hℓ hℓN f]
  exact hF'f τ

#print axioms solution

end S_ModularCurve_periodMap_heckeTLin
end P2MW
export P2MW.S_ModularCurve_periodMap_heckeTLin (solution)
