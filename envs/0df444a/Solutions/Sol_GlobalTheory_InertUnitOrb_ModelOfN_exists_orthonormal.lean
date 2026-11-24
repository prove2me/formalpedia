-- Prove2me | solution 1 for GlobalTheory.InertUnitOrb.ModelOfN.exists_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:21:07.374453+00:00
-- url     : https://prove2.me/submissions/b0e27f90-84dc-4564-a793-dc9e72ad5e95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero
import Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_herm_smul_right
import Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_herm_add_right
import Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_exists_unit_vector
import Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_fg_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.InertUnitOrb GlobalTheory.InertUnitOrb.ModelOfN
variable {K : UQ}
namespace GlobalTheory.InertUnitOrb.ModelOfN
theorem _root_.solution (n : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (h : V → V → K.E),
    (∀ y y' z, h (y + y') z = h y z + h y' z) → (∀ (a : K.E) y z, h (a • y) z = a * h y z) →
    (∀ y z, h z y = K.c (h y z)) → Module.finrank K.E V = n → ∀ L : Submodule K.O V, L.FG →
    Submodule.span K.E (L : Set V) = ⊤ → (∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) →
    ∃ v : Fin n → V, ∀ i j, h (v i) (v j) = if i = j then 1 else 0 := by
  induction n with
  | zero => intros; exact ⟨Fin.elim0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro V _ _ _ _ _ h hadd hsmul hsym hn L hfg hspan hdual
    obtain ⟨u, huL, huu⟩ := exists_unit_vector h hadd hsmul hsym (by omega) L hfg hspan hdual
    let f : V →ₗ[K.E] K.E :=
      { toFun := fun y => h y u, map_add' := fun y y' => hadd y y' u, map_smul' := fun a y => hsmul a y u }
    have hf : ∀ y, f y = h y u := fun y => rfl
    let W := LinearMap.ker f
    have hmemW : ∀ y : V, y ∈ W ↔ h y u = 0 := fun y => LinearMap.mem_ker
    have hrange : LinearMap.range f = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro a
      exact ⟨a • u, by rw [hf, hsmul, huu, mul_one]⟩
    have hfW : Module.finrank K.E W = n := by
      show Module.finrank K.E (LinearMap.ker f) = n
      have := LinearMap.finrank_range_add_finrank_ker f
      rw [hrange, finrank_top, Module.finrank_self, hn] at this
      omega
    let p : V →ₗ[K.E] W := LinearMap.codRestrict W (LinearMap.id - LinearMap.smulRight f u) (by
      intro y
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply, map_sub,
        map_smul, hf u, huu, smul_eq_mul, mul_one, sub_self])
    have hp : ∀ y, (p y : V) = y - h y u • u := fun y => rfl
    have hpL : ∀ y ∈ L, (p y : V) ∈ L := by
      intro y hy
      obtain ⟨a, ha⟩ := (hdual y).1 hy u huL
      rw [hp, ← ha, algebraMap_smul]
      exact L.sub_mem hy (L.smul_mem a huL)
    have hpW : ∀ w : W, p w = w := by
      intro w
      ext
      rw [hp, (hmemW w).1 w.2, zero_smul, sub_zero]
    let L' : Submodule K.O W := L.comap (W.subtype.restrictScalars K.O)
    have hL' : ∀ y : W, y ∈ L' ↔ (y : V) ∈ L := fun y => Iff.rfl
    have hfg' : L'.FG := by
      refine Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars K.O) Subtype.val_injective ?_
      refine fg_of_le L _ hfg ?_
      rintro _ ⟨y, hy, rfl⟩
      exact hy
    have hspan' : Submodule.span K.E (L' : Set W) = ⊤ := by
      have hsurj : Function.Surjective p := fun w => ⟨(w : V), hpW w⟩
      have h1 := Submodule.map_span p (L : Set V)
      rw [hspan, Submodule.map_top, LinearMap.range_eq_top.2 hsurj] at h1
      rw [eq_top_iff, h1]
      apply Submodule.span_mono
      rintro _ ⟨y, hy, rfl⟩
      exact (hL' _).2 (hpL y hy)
    have hdual' : ∀ y : W, y ∈ L' ↔ ∀ z ∈ L', h (y : V) (z : V) ∈ (algebraMap K.O K.E).range := by
      intro y
      rw [hL', hdual]
      constructor
      · intro H z hz
        exact H z ((hL' z).1 hz)
      · intro H z hz
        have hz' : z = (p z : V) + h z u • u := by rw [hp]; abel
        rw [hz', herm_add_right h hadd hsym, herm_smul_right h hsmul hsym, (hmemW y).1 y.2, mul_zero, add_zero]
        exact H (p z) ((hL' _).2 (hpL z hz))
    obtain ⟨w, hw⟩ := ih W (fun y z => h y z) (fun y y' z => hadd y y' z) (fun a y z => hsmul a y z)
      (fun y z => hsym y z) hfW L' hfg' hspan' hdual'
    refine ⟨Fin.cons u (fun i => (w i : V)), ?_⟩
    have hwu : ∀ i, h (w i : V) u = 0 := fun i => (hmemW _).1 (w i).2
    have huw : ∀ i, h u (w i : V) = 0 := fun i => by rw [hsym, hwu, map_zero]
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [huu]
    · simp [huw, (Fin.succ_ne_zero j).symm]
    · simp [hwu, Fin.succ_ne_zero i]
    · simp only [Fin.cons_succ, Fin.succ_inj]
      exact hw i j
end GlobalTheory.InertUnitOrb.ModelOfN
