-- Prove2me | solution 1 for MazurTransfer.closed_point_kernel_power_generator_orders
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T21:43:16.001989+00:00
-- url     : https://prove2.me/submissions/af246d0a-fc68-4def-966d-49f8e4e40ed1

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Official Anthropic FLT proof infrastructure at
6e837e75355538c7f80bab5b956861e86c4eacc2, with separately checked
arbitrary-residue-field adaptations; originals unchanged.
Design boundary: nonrational closed-point ideals and their actual valuation
orders. Named downstream consumer: divisor-class realization and surjectivity
in the literal order-13 arithmetic Picard group correspondence.
-/
import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_adicValuation_le_one
import Theorems.Thm_AlgebraicCurve_range_algebraMap_functionField_eq_iInf_of_isAffineOpen

open CategoryTheory AlgebraicGeometry AlgebraicCurve
/- Full official Anthropic FLT proof, Apache-2.0, pin 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original mathematical declarations, hypotheses and exported statement retained.
Only generated metadata and aliases normalized. Design boundary: field-extension cohomology, divisor-class comparisons and
Picard covering chart vanishing. Named downstream consumer: the full
Euler-characteristic characterization of the degree-zero Picard subfunctor
of the actual order-13 curve. -/
namespace MazurTransfer.PublicClosedPointOrderOriginal
namespace AlgebraicGeometry
end AlgebraicGeometry


universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.MazurTransfer.PublicClosedPointOrderOriginal.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace RatSec
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}} (M : X.Modules)

noncomputable abbrev rM {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) := fun y => M.presheaf.map (homOfLE h).op y

noncomputable abbrev rO {V W : X.Opens} (h : V ≤ W) : Γ(X, W) → Γ(X, V) := fun g => X.presheaf.map (homOfLE h).op g

theorem rM_rM {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    rM M h₃₂ (rM M h₂₁ y) = rM M (h₃₂.trans h₂₁) y := by
  show (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

omit M in
theorem rO_rO {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (g : Γ(X, V₁)) :
    rO h₃₂ (rO h₂₁ g) = rO (h₃₂.trans h₂₁) g := by
  show (X.presheaf.map (homOfLE h₂₁).op ≫ X.presheaf.map (homOfLE h₃₂).op).hom g = _
  rw [← Functor.map_comp]; rfl

theorem rM_self {V : X.Opens} (h : V ≤ V) (y : Γ(M, V)) : rM M h y = y := by
  show (M.presheaf.map (homOfLE h).op) y = y
  rw [Subsingleton.elim (homOfLE h) (𝟙 V), op_id, M.presheaf.map_id]; rfl

omit M in
theorem rO_self {V : X.Opens} (h : V ≤ V) (g : Γ(X, V)) : rO h g = g := by
  show (X.presheaf.map (homOfLE h).op).hom g = g
  rw [Subsingleton.elim (homOfLE h) (𝟙 V), op_id, X.presheaf.map_id]; rfl

theorem rM_smul {V W : X.Opens} (h : V ≤ W) (g : Γ(X, W)) (y : Γ(M, W)) :
    rM M h (g • y) = rO h g • rM M h y := M.map_smul _ _ _

theorem rM_add {V W : X.Opens} (h : V ≤ W) (y y' : Γ(M, W)) :
    rM M h (y + y') = rM M h y + rM M h y' := map_add _ _ _

theorem rM_zero {V W : X.Opens} (h : V ≤ W) : rM M h (0 : Γ(M, W)) = 0 := map_zero _

theorem rM_sub {V W : X.Opens} (h : V ≤ W) (y y' : Γ(M, W)) :
    rM M h (y - y') = rM M h y - rM M h y' := map_sub _ _ _

omit M in
theorem rO_one {V W : X.Opens} (h : V ≤ W) : rO h (1 : Γ(X, W)) = 1 := map_one _

omit M in
theorem rO_mul {V W : X.Opens} (h : V ≤ W) (a b : Γ(X, W)) : rO h (a * b) = rO h a * rO h b := map_mul _ _ _

omit M in
theorem rO_zero {V W : X.Opens} (h : V ≤ W) : rO h (0 : Γ(X, W)) = 0 := map_zero _

section Transport

variable (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)

theorem hat_eq {W : X.Opens} (hWV : W ≤ V) : V.ι ''ᵁ V.ι ⁻¹ᵁ W = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr hWV]

theorem le_hat {W : X.Opens} (hWV : W ≤ V) : W ≤ V.ι ''ᵁ V.ι ⁻¹ᵁ W := (hat_eq V hWV).ge
theorem hat_le {W : X.Opens} (hWV : W ≤ V) : V.ι ''ᵁ V.ι ⁻¹ᵁ W ≤ W := (hat_eq V hWV).le

noncomputable def eApp (W : X.Opens) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W) :=
  (e.hom.app (V.ι ⁻¹ᵁ W)).hom m

noncomputable def eInv (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W) :=
  (e.inv.app (V.ι ⁻¹ᵁ W)).hom a

theorem eInv_eApp (W : X.Opens) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : eInv M V e W (eApp M V e W m) = m := by
  show (e.hom.app (V.ι ⁻¹ᵁ W) ≫ e.inv.app (V.ι ⁻¹ᵁ W)).hom m = m
  erw [← _root_.AlgebraicGeometry.Scheme.Modules.Hom.comp_app, e.hom_inv_id, _root_.AlgebraicGeometry.Scheme.Modules.Hom.id_app]; rfl

theorem eApp_eInv (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) : eApp M V e W (eInv M V e W a) = a := by
  show (e.inv.app (V.ι ⁻¹ᵁ W) ≫ e.hom.app (V.ι ⁻¹ᵁ W)).hom a = a
  erw [← _root_.AlgebraicGeometry.Scheme.Modules.Hom.comp_app, e.inv_hom_id, _root_.AlgebraicGeometry.Scheme.Modules.Hom.id_app]; rfl

theorem eApp_zero (W : X.Opens) : eApp M V e W 0 = 0 := (e.hom.app (V.ι ⁻¹ᵁ W)).hom.map_zero

theorem eApp_add (W : X.Opens) (m m' : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    eApp M V e W (m + m') = eApp M V e W m + eApp M V e W m' := (e.hom.app (V.ι ⁻¹ᵁ W)).hom.map_add m m'

theorem eApp_injective (W : X.Opens) : Function.Injective (eApp M V e W) :=
  Function.LeftInverse.injective (eInv_eApp M V e W)

theorem restrict_smul_eq (W' : V.toScheme.Opens) (b : Γ(V.toScheme, W')) (m : Γ(M.restrict V.ι, W')) :
    (HSMul.hSMul (α := Γ(V.toScheme, W')) (β := Γ(M.restrict V.ι, W')) b m : Γ(M, V.ι ''ᵁ W'))
      = HSMul.hSMul (α := Γ(X, V.ι ''ᵁ W')) (β := Γ(M, V.ι ''ᵁ W')) ((Scheme.Hom.appIso V.ι W').inv b) m := rfl

theorem eApp_smul (W : X.Opens) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    eApp M V e W (a • m) = a * eApp M V e W m := by
  have hinv : (Scheme.Hom.appIso V.ι (V.ι ⁻¹ᵁ W)).inv a = a := by
    rw [Scheme.Opens.ι_appIso]; rfl
  have h := Hom.app_smul e.hom (U := V.ι ⁻¹ᵁ W) a m
  have hl := restrict_smul_eq M V (V.ι ⁻¹ᵁ W) a m
  rw [hinv] at hl
  unfold eApp
  rw [← hl]
  exact h.trans rfl

theorem eApp_res {W₁ W₂ : X.Opens} (h : W₂ ≤ W₁) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W₁)) :
    eApp M V e W₂ (rM M (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) m)
      = rO (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) (eApp M V e W₁ m) := by
  have hnat := e.hom.mapPresheaf.naturality (homOfLE (Scheme.Hom.preimage_mono V.ι h)).op
  have hx := ConcreteCategory.congr_hom hnat m
  have e1 : (Scheme.Hom.opensFunctor V.ι).map (homOfLE (Scheme.Hom.preimage_mono V.ι h))
      = homOfLE (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) := Subsingleton.elim _ _
  rw [restrict_map, e1] at hx
  exact hx

noncomputable def ψ {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : Γ(X, W) :=
  rO (le_hat V hWV) (eApp M V e W (rM M (hat_le V hWV) m))

noncomputable def ψinv {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : Γ(M, W) :=
  rM M (le_hat V hWV) (eInv M V e W (rO (hat_le V hWV) a))

theorem rM_roundtrip {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : rM M (le_hat V hWV) (rM M (hat_le V hWV) m) = m := by
  rw [rM_rM, rM_self]
theorem rM_roundtrip' {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    rM M (hat_le V hWV) (rM M (le_hat V hWV) m) = m := by
  rw [rM_rM, rM_self]
omit M e in
theorem rO_roundtrip {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : rO (le_hat V hWV) (rO (hat_le V hWV) a) = a := by
  rw [rO_rO, rO_self]
omit M e in
theorem rO_roundtrip' {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, V.ι ''ᵁ V.ι ⁻¹ᵁ W)) :
    rO (hat_le V hWV) (rO (le_hat V hWV) a) = a := by
  rw [rO_rO, rO_self]

theorem ψ_ψinv {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) : ψ M V e hWV (ψinv M V e hWV a) = a := by
  simp only [ψ, ψinv]
  rw [rM_roundtrip' M V hWV, eApp_eInv, rO_roundtrip V hWV]

theorem ψinv_ψ {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) : ψinv M V e hWV (ψ M V e hWV m) = m := by
  simp only [ψ, ψinv]
  rw [rO_roundtrip' V hWV, eInv_eApp, rM_roundtrip M V hWV]

theorem ψ_injective {W : X.Opens} (hWV : W ≤ V) : Function.Injective (ψ M V e hWV) :=
  Function.LeftInverse.injective (ψinv_ψ M V e hWV)

theorem ψ_zero {W : X.Opens} (hWV : W ≤ V) : ψ M V e hWV 0 = 0 := by
  simp only [ψ]
  show rO (le_hat V hWV) (eApp M V e W ((M.presheaf.map _) 0)) = 0
  rw [map_zero, eApp_zero]; exact map_zero _

theorem ψ_add {W : X.Opens} (hWV : W ≤ V) (m m' : Γ(M, W)) :
    ψ M V e hWV (m + m') = ψ M V e hWV m + ψ M V e hWV m' := by
  simp only [ψ]
  rw [rM_add, eApp_add]
  exact map_add _ _ _

theorem ψ_smul {W : X.Opens} (hWV : W ≤ V) (a : Γ(X, W)) (m : Γ(M, W)) :
    ψ M V e hWV (a • m) = a * ψ M V e hWV m := by
  simp only [ψ]
  rw [rM_smul, eApp_smul]
  show (X.presheaf.map _).hom (_ * _) = a * _
  rw [map_mul]
  congr 1
  exact rO_roundtrip V hWV a

theorem ψ_res {W₁ W₂ : X.Opens} (h₁ : W₁ ≤ V) (h : W₂ ≤ W₁) (m : Γ(M, W₁)) :
    ψ M V e (h.trans h₁) (rM M h m) = rO h (ψ M V e h₁ m) := by
  simp only [ψ]
  have lhs : rM M (hat_le V (h.trans h₁)) (rM M h m)
      = rM M (Scheme.Hom.image_mono V.ι (Scheme.Hom.preimage_mono V.ι h)) (rM M (hat_le V h₁) m) := by
    rw [rM_rM, rM_rM]
  rw [lhs, eApp_res M V e h, rO_rO, rO_rO]

noncomputable def frame : Γ(M, V) := ψinv M V e le_rfl 1

theorem ψ_frame : ψ M V e le_rfl (frame M V e) = 1 := ψ_ψinv M V e le_rfl 1

theorem ψ_rM_frame {W : X.Opens} (hWV : W ≤ V) : ψ M V e hWV (rM M hWV (frame M V e)) = 1 := by
  have h := ψ_res M V e le_rfl hWV (frame M V e)
  rw [ψ_frame, rO_one] at h
  exact h

theorem eq_smul_frame {W : X.Opens} (hWV : W ≤ V) (m : Γ(M, W)) :
    m = ψ M V e hWV m • rM M hWV (frame M V e) := by
  apply ψ_injective M V e hWV
  rw [ψ_smul, ψ_rM_frame, mul_one]

end Transport

section Integral

variable [IsIntegral X]

omit M in
theorem nonempty_inf (U W : X.Opens) [hU : Nonempty U] [hW : Nonempty W] : Nonempty (U ⊓ W : X.Opens) := by
  obtain ⟨⟨u, hu⟩⟩ := hU
  obtain ⟨⟨w, hw⟩⟩ := hW
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen ⟨u, hu⟩ ⟨w, hw⟩
  exact ⟨⟨z, hz⟩⟩

omit M in

noncomputable abbrev alg (U : X.Opens) [Nonempty U] (a : Γ(X, U)) : X.functionField :=
  (X.germToFunctionField U).hom a

omit M in
theorem alg_rO {U W : X.Opens} [Nonempty U] [Nonempty W] (h : W ≤ U) (a : Γ(X, U)) :
    alg W (rO h a) = alg U a := by
  show (X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField W).hom a = _
  unfold Scheme.germToFunctionField
  rw [TopCat.Presheaf.germ_res]

omit M in
theorem alg_injective (U : X.Opens) [Nonempty U] : Function.Injective (alg (X := X) U) :=
  Scheme.germToFunctionField_injective X U

omit M in
theorem rO_injective {U W : X.Opens} [Nonempty U] [Nonempty W] (h : W ≤ U) :
    Function.Injective (rO (X := X) h) := by
  intro a b hab
  apply alg_injective U
  rw [← alg_rO h, ← alg_rO h, hab]

omit M in
theorem alg_one (U : X.Opens) [Nonempty U] : alg U (1 : Γ(X, U)) = 1 := map_one _

omit M in
theorem alg_zero (U : X.Opens) [Nonempty U] : alg U (0 : Γ(X, U)) = 0 := map_zero _

omit M in
theorem alg_add (U : X.Opens) [Nonempty U] (a b : Γ(X, U)) : alg U (a + b) = alg U a + alg U b := map_add _ _ _

omit M in
theorem alg_mul (U : X.Opens) [Nonempty U] (a b : Γ(X, U)) : alg U (a * b) = alg U a * alg U b := map_mul _ _ _

end Integral

section Places

open AlgebraicCurve WithZero

variable {K : Type u} [Field K] (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [SmoothOfRelativeDimension 1 x]

omit M in

theorem adicValuation_alg_le_one (W : X.Opens) (y : X) (hyW : y ∈ W) (hy : IsClosed ({y} : Set X))
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring)
    (a : Γ(X, W)) :
    letI := (baseToFunctionField x).toAlgebra
    haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
    v.adicValuation (alg W a) ≤ 1 := by
  letI := (baseToFunctionField x).toAlgebra
  haveI : Nonempty W := ⟨⟨y, hyW⟩⟩

  obtain ⟨W', hW'aff, hyW', hW'W⟩ :=
    (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hyW
  haveI : Nonempty W' := ⟨⟨y, hyW'⟩⟩
  rw [← alg_rO hW'W a]
  apply (_root_.P2M.Dup.AlgebraicCurve.Place.mem_iff_adicValuation_le_one v).mp
  have hmem : alg W' (rO hW'W a) ∈ (algebraMap Γ(X, W') X.functionField).range := ⟨rO hW'W a, rfl⟩
  rw [range_algebraMap_functionField_eq_iInf_of_isAffineOpen x W' hW'aff] at hmem
  have h2 := (Subring.mem_iInf.mp hmem) v
  have h3 := (Subring.mem_iInf.mp h2) ⟨y, hyW', hy, hv⟩
  exact h3

def IsGeneratorAt (U : X.Opens) (s : Γ(M, U)) (y : X) : Prop :=
  ∀ (W : X.Opens) (h : W ≤ U), y ∈ W → ∀ m : Γ(M, W), ∃ a : Γ(X, W), m = a • rM M h s

omit x [IsIntegral X] in
theorem isGeneratorAt_frame (V : X.Opens) (e : M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
    (y : X) : IsGeneratorAt M V (frame M V e) y :=
  fun _ h _ m => ⟨ψ M V e h m, eq_smul_frame M V e h m⟩

omit x [IsIntegral X] in
theorem isGeneratorAt_rM {U W : X.Opens} (h : W ≤ U) (s : Γ(M, U)) (y : X) (hs : IsGeneratorAt M U s y) :
    IsGeneratorAt M W (rM M h s) y := by
  intro W' h' hyW' m
  obtain ⟨a, ha⟩ := hs W' (h'.trans h) hyW' m
  exact ⟨a, by rw [rM_rM]; exact ha⟩

end Places

end AlgebraicGeometry.Scheme.Modules.RatSec

namespace AlgebraicGeometry
namespace Scheme
namespace Modules
namespace RatSec
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

section Centre

open AlgebraicCurve WithZero

variable {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]

theorem alg_pow (W : X.Opens) [Nonempty W] (a : Γ(X, W)) (n : ℕ) : alg W (a ^ n) = alg W a ^ n :=
  map_pow _ _ _

theorem alg_eq_algebraMap_germ (W : X.Opens) (y : X) (hyW : y ∈ W) (a : Γ(X, W)) :
    haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
    alg W a = algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ W y hyW a) := by
  haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
  show (X.presheaf.germ W (genericPoint X) _) a = (X.presheaf.stalkSpecializes _) ((X.presheaf.germ W y hyW) a)
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

theorem adicValuation_alg_le_one' (W : X.Opens) (y : X) (hyW : y ∈ W)
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring)
    (a : Γ(X, W)) :
    letI := (baseToFunctionField x).toAlgebra
    haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
    v.adicValuation (alg W a) ≤ 1 := by
  letI := (baseToFunctionField x).toAlgebra
  haveI : Nonempty W := ⟨⟨y, hyW⟩⟩
  apply (_root_.P2M.Dup.AlgebraicCurve.Place.mem_iff_adicValuation_le_one v).mp
  show alg W a ∈ v.toValuationSubring.toSubring
  rw [← hv, alg_eq_algebraMap_germ W y hyW a]
  exact ⟨_, rfl⟩

theorem adicValuation_algebraMap_stalk_le_one (y : X)
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring)
    (q : X.presheaf.stalk y) :
    letI := (baseToFunctionField x).toAlgebra
    v.adicValuation (algebraMap (X.presheaf.stalk y) X.functionField q) ≤ 1 := by
  letI := (baseToFunctionField x).toAlgebra
  apply (_root_.P2M.Dup.AlgebraicCurve.Place.mem_iff_adicValuation_le_one v).mp
  show _ ∈ v.toValuationSubring.toSubring
  rw [← hv]
  exact ⟨_, rfl⟩

theorem adicValuation_algebraMap_stalk_eq_one (y : X)
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring)
    (q : X.presheaf.stalk y) (hq : IsUnit q) :
    letI := (baseToFunctionField x).toAlgebra
    v.adicValuation (algebraMap (X.presheaf.stalk y) X.functionField q) = 1 := by
  letI := (baseToFunctionField x).toAlgebra
  obtain ⟨w, hw⟩ := hq.exists_right_inv
  have h1 := adicValuation_algebraMap_stalk_le_one x y v hv q
  have h2 := adicValuation_algebraMap_stalk_le_one x y v hv w
  have h3 : v.adicValuation (algebraMap (X.presheaf.stalk y) X.functionField q) *
      v.adicValuation (algebraMap (X.presheaf.stalk y) X.functionField w) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, hw, map_one, Valuation.map_one]
  apply le_antisymm h1
  calc (1 : ℤᵐ⁰) = _ * _ := h3.symm
    _ ≤ v.adicValuation (algebraMap (X.presheaf.stalk y) X.functionField q) * 1 :=
        mul_le_mul_right h2 _
    _ = _ := mul_one _

theorem adicValuation_algebraMap_stalk_lt_one (y : X)
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField)
    (hv : letI := (baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring)
    (q : X.presheaf.stalk y) (hq : ¬ IsUnit q) :
    letI := (baseToFunctionField x).toAlgebra
    v.adicValuation (algebraMap (X.presheaf.stalk y) X.functionField q) < 1 := by
  letI := (baseToFunctionField x).toAlgebra
  have h1 := adicValuation_algebraMap_stalk_le_one x y v hv q
  refine lt_of_le_of_ne h1 ?_
  intro heq
  apply hq

  have hmem : algebraMap (X.presheaf.stalk y) X.functionField q ∈ v.toValuationSubring :=
    (_root_.P2M.Dup.AlgebraicCurve.Place.mem_iff_adicValuation_le_one v).mpr h1
  have hunit : IsUnit (⟨_, hmem⟩ : v.toValuationSubring) := (v.adicValuation_coe_eq_one_iff ⟨_, hmem⟩).mp heq
  obtain ⟨w, hw⟩ := hunit.exists_right_inv
  have hwmem : (w : X.functionField) ∈ (algebraMap (X.presheaf.stalk y) X.functionField).range := by
    rw [hv]; exact w.2
  obtain ⟨w', hw'⟩ := hwmem
  have hprod : algebraMap (X.presheaf.stalk y) X.functionField (q * w') = 1 := by
    rw [map_mul, hw']
    exact congrArg Subtype.val hw
  have hinj : Function.Injective (algebraMap (X.presheaf.stalk y) X.functionField) :=
    IsFractionRing.injective _ _
  have : q * w' = 1 := hinj (by rw [hprod, map_one])
  exact isUnit_iff_exists_inv.mpr ⟨w', this⟩

omit [IsIntegral X] in

theorem le_exp_neg_one_of_lt_one {u : ℤᵐ⁰} (hu : u < 1) : u ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne u 0 with rfl | h0
  · exact zero_le'
  · obtain ⟨m, rfl⟩ : ∃ m : ℤ, exp m = u := ⟨WithZero.log u, WithZero.exp_log h0⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hu
    rw [WithZero.exp_le_exp]
    omega

end Centre

end AlgebraicGeometry.Scheme.Modules.RatSec

end MazurTransfer.PublicClosedPointOrderOriginal

universe u

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from the complete official Anthropic FLT kernel-order proof at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. Its rational section
condition is used only to establish a closed immersion. Here the residue field
may differ from the base field, and the closed immersion is explicit; the full
valuation and localization proof is retained. The original theorem is unchanged.
Design boundary: kernel ideals of arbitrary closed points have valuation one
at their own place and zero elsewhere. Named downstream consumer: realization
of degree-zero function-field divisor classes on the actual order-13 curve.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicCurve WithZero
open MazurTransfer.PublicClosedPointOrderOriginal.AlgebraicGeometry.Scheme.Modules.RatSec

theorem MazurTransfer.PublicClosedPointOrderProof.ord_eq_of_closedPoint_ker_pow_ideal_eq_span
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x]
    {L : Type u} [Field L] (P : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion P] (n : ℕ)
    (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (hg : (P.ker ^ n).ideal ⟨U, hU⟩ = Ideal.span {g})
    (y : X) (hyU : y ∈ U) (hy : IsClosed ({y} : Set X))
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K X.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    (P.base (IsLocalRing.closedPoint L) = y → v.ord (algebraMap Γ(X, U) X.functionField g) = n) ∧
      (P.base (IsLocalRing.closedPoint L) ≠ y → v.ord (algebraMap Γ(X, U) X.functionField g) = 0) := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
  set pt : X := P.base (IsLocalRing.closedPoint L) with hpt

  have hrange : Set.range P.base = {pt} := by
    ext z
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, rfl⟩
      rw [Subsingleton.elim w (IsLocalRing.closedPoint L)]
    · rintro rfl
      exact ⟨_, rfl⟩
  have hptc : IsClosed ({pt} : Set X) := hrange ▸ P.isClosedEmbedding.isClosed_range
  have hsupp : ((P.ker).support : Set X) = {pt} := by
    rw [Scheme.Hom.support_ker, hrange, hptc.closure_eq]

  have hval1 : ∀ (a : Γ(X, U)), IsUnit (X.presheaf.germ U y hyU a) → v.adicValuation (alg U a) = 1 := by
    intro a ha
    rw [alg_eq_algebraMap_germ U y hyU a]
    exact adicValuation_algebraMap_stalk_eq_one x y v hv _ ha
  have hval2 : ∀ (a : Γ(X, U)), ¬ IsUnit (X.presheaf.germ U y hyU a) →
      v.adicValuation (alg U a) ≤ exp (-1 : ℤ) := by
    intro a ha
    rw [alg_eq_algebraMap_germ U y hyU a]
    exact le_exp_neg_one_of_lt_one (adicValuation_algebraMap_stalk_lt_one x y v hv _ ha)

  let J : ℕ → Ideal Γ(X, U) := fun m =>
    { carrier := {a | v.adicValuation (alg U a) ≤ exp (-(m : ℤ))}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [alg_add]
        exact (Valuation.map_add _ _ _).trans (max_le ha hb)
      zero_mem' := by simp only [Set.mem_setOf_eq, alg_zero, Valuation.map_zero]; exact zero_le'
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at ha ⊢
        rw [alg_mul, Valuation.map_mul]
        calc _ ≤ 1 * v.adicValuation (alg U a) :=
              mul_le_mul_left (adicValuation_alg_le_one' x U y hyU v hv c) _
          _ ≤ exp (-(m : ℤ)) := by rw [one_mul]; exact ha }
  have hJ : ∀ a m, a ∈ J m ↔ v.adicValuation (alg U a) ≤ exp (-(m : ℤ)) := fun a m => Iff.rfl
  have hJmul : ∀ m k, J m * J k ≤ J (m + k) := by
    intro m k
    rw [Ideal.mul_le]
    intro a ha b hb
    rw [hJ] at ha hb ⊢
    rw [alg_mul, Valuation.map_mul, Nat.cast_add, neg_add, WithZero.exp_add]
    exact mul_le_mul' ha hb

  by_cases hyp : pt = y
  ·
    subst hyp
    refine ⟨fun _ => ?_, fun h => (h rfl).elim⟩
    show v.ord (alg U g) = (n : ℤ)
    let Q : Ideal Γ(X, U) := (hU.primeIdealOf ⟨pt, hyU⟩).asIdeal
    haveI hQp : Q.IsPrime := (hU.primeIdealOf ⟨pt, hyU⟩).isPrime
    letI algSt : Algebra Γ(X, U) (X.presheaf.stalk pt) := (X.presheaf.germ U pt hyU).hom.toAlgebra
    haveI : IsLocalization.AtPrime (X.presheaf.stalk pt) Q := hU.isLocalization_stalk ⟨pt, hyU⟩
    have halgSt : ∀ a : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk pt) a = X.presheaf.germ U pt hyU a :=
      fun a => rfl

    have hQmem : ∀ a : Γ(X, U), a ∈ Q ↔ ¬ IsUnit (X.presheaf.germ U pt hyU a) := by
      intro a
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk pt) Q a, IsLocalRing.mem_maximalIdeal,
        mem_nonunits_iff]
      rfl

    have hker : P.ker.ideal ⟨U, hU⟩ = RingHom.ker (P.app U).hom := Scheme.Hom.ker_apply P ⟨U, hU⟩
    have hle : P.ker.ideal ⟨U, hU⟩ ≤ Q := by
      intro a ha
      rw [hker, RingHom.mem_ker] at ha
      rw [hQmem]
      intro hu
      have hmem : pt ∈ X.basicOpen a := (X.mem_basicOpen a pt hyU).mpr hu
      have : IsLocalRing.closedPoint L ∈ P ⁻¹ᵁ X.basicOpen a := hmem
      rw [Scheme.Hom.preimage_basicOpen, ha, Scheme.basicOpen_zero] at this
      exact this

    have hge : Q ≤ P.ker.ideal ⟨U, hU⟩ := by
      intro a ha
      rw [hQmem] at ha
      rw [hker, RingHom.mem_ker]

      have hcp : IsLocalRing.closedPoint L = genericPoint (Spec (CommRingCat.of L)) := Subsingleton.elim _ _
      have hfield : ∀ z : (Spec (CommRingCat.of L)).presheaf.stalk (IsLocalRing.closedPoint L), z ≠ 0 → IsUnit z := by
        rw [hcp]
        intro z hz
        obtain ⟨w, hw⟩ := (Field.toIsField (Spec (CommRingCat.of L)).functionField).mul_inv_cancel hz
        exact isUnit_iff_exists_inv.mpr ⟨w, hw⟩
      have key := Scheme.Hom.germ_stalkMap_apply P U (IsLocalRing.closedPoint L) hyU a
      letI : IsLocalHom (P.stalkMap (IsLocalRing.closedPoint L)).hom := P.prop _
      have hnu : ¬ IsUnit ((P.stalkMap (IsLocalRing.closedPoint L)).hom (X.presheaf.germ U pt hyU a)) :=
        fun h => ha ((isUnit_map_iff (P.stalkMap (IsLocalRing.closedPoint L)).hom _).mp h)
      have hzero : (Spec (CommRingCat.of L)).presheaf.germ (P ⁻¹ᵁ U) (IsLocalRing.closedPoint L) hyU (P.app U a) = 0 := by
        by_contra hne
        apply hnu
        have hu := hfield _ hne
        rw [← key] at hu
        exact hu
      exact germ_injective_of_isIntegral _ (IsLocalRing.closedPoint L) hyU (by rw [hzero, map_zero])
    have hQeq : P.ker.ideal ⟨U, hU⟩ = Q := le_antisymm hle hge

    have hpow : (P.ker ^ n).ideal ⟨U, hU⟩ = Q ^ n := by
      rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, hQeq]
    rw [hpow] at hg

    have hQJ : ∀ m, Q ^ m ≤ J m := by
      intro m
      induction m with
      | zero =>
        intro a _
        rw [hJ]
        simp only [Nat.cast_zero, neg_zero, WithZero.exp_zero]
        exact adicValuation_alg_le_one' x U pt hyU v hv a
      | succ m ih =>
        rw [pow_succ]
        refine le_trans (Ideal.mul_mono ih ?_) (hJmul m 1)
        intro a ha
        rw [hJ, Nat.cast_one]
        exact hval2 a ((hQmem a).mp ha)
    have hg_le : v.adicValuation (alg U g) ≤ exp (-(n : ℤ)) := by
      rw [← hJ]
      exact hQJ n (hg ▸ Ideal.mem_span_singleton_self g)

    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    have hϖmem : (ϖ : X.functionField) ∈ (algebraMap (X.presheaf.stalk pt) X.functionField).range := by
      rw [hv]; exact ϖ.2
    obtain ⟨q, hq⟩ := hϖmem
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective Q.primeCompl q

    have hspec : q * algebraMap Γ(X, U) (X.presheaf.stalk pt) b = algebraMap Γ(X, U) (X.presheaf.stalk pt) a := by
      rw [← hab]; exact IsLocalization.mk'_spec _ a b
    have hbunit : IsUnit (X.presheaf.germ U pt hyU b) := by
      have := (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk pt) Q (b : Γ(X, U))).mpr b.2
      exact this
    have hb1 : v.adicValuation (alg U b) = 1 := hval1 b hbunit
    have halga : alg U a = (ϖ : X.functionField) * alg U b := by
      rw [alg_eq_algebraMap_germ U pt hyU a, alg_eq_algebraMap_germ U pt hyU b, ← hq, ← map_mul]
      congr 1
      exact hspec.symm
    have hϖ0 : (ϖ : X.functionField) ≠ 0 := by
      intro h; exact hϖ.ne_zero (Subtype.ext h)
    have hb0 : alg U b ≠ 0 := by
      intro h; rw [h, Valuation.map_zero] at hb1; exact zero_ne_one hb1
    have horda : v.ord (alg U a) = 1 := by
      rw [halga, Place.ord_mul _ hϖ0 hb0, Place.ord_coe_irreducible _ hϖ]
      simp only [Place.ord, hb1, Valuation.map_one, WithZero.log_one, neg_zero, add_zero]
    have haQ : a ∈ Q := by
      rw [hQmem]
      intro hu

      have hqu : IsUnit q := by
        have h2 : IsUnit (q * algebraMap Γ(X, U) (X.presheaf.stalk pt) b) := by rw [hspec]; exact hu
        exact isUnit_of_mul_isUnit_left h2
      have := adicValuation_algebraMap_stalk_eq_one x pt v hv q hqu
      rw [hq, Place.adicValuation_coe_irreducible _ hϖ] at this
      exact absurd this (by decide)

    have han : a ^ n ∈ Ideal.span {g} := hg ▸ Ideal.pow_mem_pow haQ n
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp han
    have ha0 : alg U a ≠ 0 := by
      intro h
      have := horda
      rw [h, Place.ord_zero] at this
      exact zero_ne_one this
    have hg0 : alg U g ≠ 0 := by
      intro h0
      have : alg U (a ^ n) = 0 := by rw [← hc, alg_mul, h0, mul_zero]
      rw [alg_pow] at this
      exact pow_ne_zero n ha0 this
    have hc0 : alg U c ≠ 0 := by
      intro h0
      have : alg U (a ^ n) = 0 := by rw [← hc, alg_mul, h0, zero_mul]
      rw [alg_pow] at this
      exact pow_ne_zero n ha0 this

    have hordan : v.ord (alg U (a ^ n)) = n := by
      rw [alg_pow, ← zpow_natCast, Place.ord_zpow, horda, mul_one]
    have hup : v.ord (alg U g) ≤ n := by
      have e1 : v.ord (alg U (a ^ n)) = v.ord (alg U c) + v.ord (alg U g) := by
        rw [← hc, alg_mul, Place.ord_mul _ hc0 hg0]
      have e2 : 0 ≤ v.ord (alg U c) := by
        have h1 := adicValuation_alg_le_one' x U pt hyU v hv c
        have h2 : v.adicValuation (alg U c) = exp (-(v.ord (alg U c))) := by
          simp only [Place.ord, neg_neg, WithZero.exp_log (Place.adicValuation_ne_zero _ hc0)]
        rw [h2, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
        omega
      omega

    have hdown : (n : ℤ) ≤ v.ord (alg U g) := by
      have h1 : v.adicValuation (alg U g) = exp (-(v.ord (alg U g))) := by
        simp only [Place.ord, neg_neg, WithZero.exp_log (Place.adicValuation_ne_zero _ hg0)]
      rw [h1, WithZero.exp_le_exp] at hg_le
      omega
    exact le_antisymm hup hdown
  ·
    refine ⟨fun h => (hyp h).elim, fun _ => ?_⟩
    have hy' : y ∉ (P.ker).support := by
      rw [← SetLike.mem_coe, hsupp, Set.mem_singleton_iff]
      exact fun h => hyp h.symm
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hyU, Scheme.mem_zeroLocus_iff] at hy'
    simp only [not_forall, not_not, exists_prop] at hy'
    obtain ⟨a, ha, hya⟩ := hy'
    have han : a ^ n ∈ (P.ker ^ n).ideal ⟨U, hU⟩ := by
      rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
      exact Ideal.pow_mem_pow ha n
    rw [hg] at han
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp han
    have hau : IsUnit (X.presheaf.germ U y hyU a) := (X.mem_basicOpen a y hyU).mp hya
    have hgu : IsUnit (X.presheaf.germ U y hyU g) := by
      have : IsUnit (X.presheaf.germ U y hyU (a ^ n)) := by rw [map_pow]; exact hau.pow n
      rw [← hc, map_mul] at this
      exact isUnit_of_mul_isUnit_right this
    have h1 := hval1 g hgu
    show v.ord (alg U g) = 0
    simp only [Place.ord, h1, WithZero.log_one, neg_zero]


#print axioms MazurTransfer.PublicClosedPointOrderProof.ord_eq_of_closedPoint_ker_pow_ideal_eq_span

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x]
    {L : Type u} [Field L] (P : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion P] (n : ℕ)
    (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (hg : (P.ker ^ n).ideal ⟨U, hU⟩ = Ideal.span {g})
    (y : X) (hyU : y ∈ U) (hy : IsClosed ({y} : Set X))
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K X.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    (P.base (IsLocalRing.closedPoint L) = y → v.ord (algebraMap Γ(X, U) X.functionField g) = n) ∧
      (P.base (IsLocalRing.closedPoint L) ≠ y → v.ord (algebraMap Γ(X, U) X.functionField g) = 0) := by exact MazurTransfer.PublicClosedPointOrderProof.ord_eq_of_closedPoint_ker_pow_ideal_eq_span x P n U hU g hg y hyU hy v hv

#print axioms solution
