-- Prove2me | solution 1 for ModularCurve.ComplexPlaceDictionary.restrictAlong_pt_heckeAlphaBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/975bf39e-f790-58fb-a523-1a77eead3a35

import Mathlib
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_realize_eq_div
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeAlphaBar
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

noncomputable section

p2m_open "UpperHalfPlane Filter ModularCurve P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeAlphaBar.ModularCurve AlgebraicCurve"
open scoped MatrixGroups Topology Manifold

namespace ModularCurve
p2m_export "ModularCurve" "realize ComplexPlaceDictionary modularFunctionFieldFull laurentBaseChange heckeAlphaBar coe_heckeAlphaBar HeckeAlphaBarIntegral exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange realize_eq_div"
namespace RestrictAlongPtHeckeAlphaBar
p2m_open "ModularCurve"

def restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ} (f : ModularForm Γ k)
    [Γ'.HasDetPlusMinusOne] : ModularForm Γ' k where
  toSlashInvariantForm := ⟨f, fun γ hγ => SlashInvariantForm.slash_action_eqn f γ (hle hγ)⟩
  holo' := f.holo'
  bdd_at_cusps' := fun hc => f.bdd_at_cusps' (hc.mono hle)

theorem coe_restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ}
    (f : ModularForm Γ k) [Γ'.HasDetPlusMinusOne] :
    ((restrict hle f : ModularForm Γ' k) : ℍ → ℂ) = f := rfl

theorem Gamma0_mul_le (N ℓ : ℕ) :
    ((CongruenceSubgroup.Gamma0 (N * ℓ) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  apply Subgroup.map_mono
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
  have h : ((N : ℤ) : ZMod N) = 0 := by simp
  have := (ZMod.castHom (dvd_mul_right N ℓ) (ZMod N)).congr_arg hγ
  rw [map_zero, ZMod.castHom_apply, ZMod.cast_intCast (dvd_mul_right N ℓ)] at this
  exact this

variable {N : ℕ}

theorem coe_eq_zero_iff {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    (f : ℍ → ℂ) = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact DFunLike.coe_injective (h.trans (ModularForm.coe_zero).symm)
  · rintro rfl; rfl

theorem eventually_ne_zero {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : f ≠ 0) (τ : ℍ) : ∀ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w ≠ 0 := by
  by_contra hcon
  have hfr : ∃ᶠ w in 𝓝[≠] τ, (f : ℍ → ℂ) w = 0 := by
    simpa [Filter.not_eventually] using hcon
  exact hf ((coe_eq_zero_iff f).mp (eq_zero_of_frequently (ModularFormClass.holo f) hfr))

theorem mem_restrictAlong_iff {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (x : F) :
    x ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ x ∈ w.toValuationSubring :=
  Iff.rfl

theorem isBoundedUnder_congr {α : Type*} {l : Filter α} {u v : α → ℝ} (h : u =ᶠ[l] v) :
    IsBoundedUnder (· ≤ ·) l u ↔ IsBoundedUnder (· ≤ ·) l v :=
  ⟨fun hu => hu.mono_le h.symm.le, fun hv => hv.mono_le h.le⟩

theorem realize_eventuallyEq_realize_mul [NeZero N] (ℓ : ℕ) (x : LaurentSeries ℂ)
    (hx : x ∈ laurentBaseChange ℂ (modularFunctionFieldFull N)) (τ : ℍ) :
    (fun z : ℍ => realize N x z) =ᶠ[𝓝[≠] τ] fun z : ℍ => realize (N * ℓ) x z := by
  obtain ⟨k, g, h, hh, hgh⟩ :=
    exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N x hx
  haveI : ((CongruenceSubgroup.Gamma0 (N * ℓ) : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).HasDetPlusMinusOne := inferInstance
  let g' : ModularForm (CongruenceSubgroup.Gamma0 (N * ℓ)) k := restrict (Gamma0_mul_le N ℓ) g
  let h' : ModularForm (CongruenceSubgroup.Gamma0 (N * ℓ)) k := restrict (Gamma0_mul_le N ℓ) h
  have hgh' : x * ((qExpansion 1 (h' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (g' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := hgh
  filter_upwards [eventually_ne_zero h hh τ] with z hz
  rw [realize_eq_div N g h x hgh z hz, realize_eq_div (N * ℓ) g' h' x hgh' z hz]
  rfl

end ModularCurve.RestrictAlongPtHeckeAlphaBar

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeAlphaBar.ModularCurve AlgebraicCurve ModularCurve.RestrictAlongPtHeckeAlphaBar Filter in
open scoped Topology in
theorem solution
    {N : ℕ} [NeZero N] (ℓ : ℕ) [NeZero ℓ] (D : ModularCurve.ComplexPlaceDictionary N)
    (D' : ModularCurve.ComplexPlaceDictionary (N * ℓ))
    (hα : ModularCurve.HeckeAlphaBarIntegral ℂ N ℓ) (τ : UpperHalfPlane) :
    (D'.pt τ).restrictAlong (ModularCurve.heckeAlphaBar ℂ N ℓ) hα = D.pt τ := by
  apply Place.ext
  ext x
  rw [mem_restrictAlong_iff, D'.mem_pt_iff, D.mem_pt_iff, coe_heckeAlphaBar]
  have h := (realize_eventuallyEq_realize_mul ℓ (x : LaurentSeries ℂ) x.2 τ).fun_comp (‖·‖)
  exact (isBoundedUnder_congr h).symm

end S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeAlphaBar
end P2MW
export P2MW.S_ModularCurve_ComplexPlaceDictionary_restrictAlong_pt_heckeAlphaBar (solution)
