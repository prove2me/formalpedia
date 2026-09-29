-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_modularFunctionFieldC_apply_jGeomGen_eq_comp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/78026f9d-d28c-5244-b75e-8ac4c51a0da3

import Mathlib
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularEquationQ
import Theorems.Thm_ModularCurve_existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_irreducible_map_adjoin_jqNModC
import Theorems.Thm_ModularCurve_ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_dedekindPsi_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_modularFunctionFieldC_apply_jGeomGen_eq_comp
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve IntermediateField

namespace B5

section Transport

variable {κ E : Type*} [Field κ] [Field E] [Algebra κ E]

theorem finiteDimensional_adjoin_of_extendScalars (B : IntermediateField κ E) (a : ↥B)
    (h : IntermediateField.adjoin κ ({(a : E)} : Set E) ≤ B)
    [hfin : FiniteDimensional ↥(IntermediateField.adjoin κ ({(a : E)} : Set E)) ↥(extendScalars h)] :
    FiniteDimensional ↥(IntermediateField.adjoin κ ({a} : Set ↥B)) ↥B := by
  classical
  set A : IntermediateField κ E := IntermediateField.adjoin κ ({(a : E)} : Set E) with hAdef
  set A' : IntermediateField κ ↥B := IntermediateField.adjoin κ ({a} : Set ↥B) with hA'def
  have hlift : IntermediateField.lift A' = A := by
    rw [hA'def, IntermediateField.lift_adjoin, Set.image_singleton]

  have hmemA' : ∀ x : ↥A, (⟨(x : E), h x.2⟩ : ↥B) ∈ A' := by
    intro x
    have hx : (x : E) ∈ IntermediateField.lift A' := by rw [hlift]; exact x.2
    rw [IntermediateField.lift, IntermediateField.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : (⟨(x : E), h x.2⟩ : ↥B) = y := Subtype.ext hyx.symm
    rw [this]; exact hy

  let φ : ↥(extendScalars h) →+ ↥B :=
    { toFun := fun x => ⟨(x : E), (IntermediateField.mem_extendScalars h).mp x.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφsmul : ∀ (c : ↥A) (x : ↥(extendScalars h)),
      φ (c • x) = (⟨⟨(c : E), h c.2⟩, hmemA' c⟩ : ↥A') • φ x := by
    intro c x
    apply Subtype.ext
    show ((c • x : ↥(extendScalars h)) : E) = (((⟨⟨(c : E), h c.2⟩, hmemA' c⟩ : ↥A') • φ x : ↥B) : E)
    rw [Algebra.smul_def, Algebra.smul_def]
    rfl
  obtain ⟨s, hs⟩ := Module.finite_def.mp hfin
  refine Module.finite_def.mpr ⟨s.image φ, ?_⟩
  rw [eq_top_iff]
  rintro b -
  have hb : (⟨(b : E), (IntermediateField.mem_extendScalars h).mpr b.2⟩ : ↥(extendScalars h)) ∈
      Submodule.span ↥A (s : Set ↥(extendScalars h)) := by rw [hs]; trivial
  have key : ∀ x : ↥(extendScalars h), x ∈ Submodule.span ↥A (s : Set ↥(extendScalars h)) →
      φ x ∈ Submodule.span ↥A' ((s.image φ : Finset ↥B) : Set ↥B) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (by rw [Finset.coe_image]; exact Set.mem_image_of_mem _ hy)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [hφsmul]; exact Submodule.smul_mem _ _ hy
  have := key _ hb
  have hφb : φ ⟨(b : E), (IntermediateField.mem_extendScalars h).mpr b.2⟩ = b := Subtype.ext rfl
  rwa [hφb] at this

end Transport

theorem finiteDimensional_adjoin_jGeomGen
    (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M) :
    FiniteDimensional ↥(IntermediateField.adjoin κ ({ModularCurve.jGeomGen κ M} : Set ↥(ModularCurve.modularFunctionFieldC κ M)))
      ↥(ModularCurve.modularFunctionFieldC κ M) := by
  have h : IntermediateField.adjoin κ ({((ModularCurve.jGeomGen κ M : ↥(ModularCurve.modularFunctionFieldC κ M)) : LaurentSeries κ)} :
      Set (LaurentSeries κ)) ≤ ModularCurve.modularFunctionFieldC κ M :=
    IntermediateField.adjoin_simple_le_iff.mpr (ModularCurve.jGeomGen κ M).2
  have hrel := ModularCurve.relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi κ M p hpM
  have hfin : FiniteDimensional ↥(IntermediateField.adjoin κ ({((ModularCurve.jGeomGen κ M :
      ↥(ModularCurve.modularFunctionFieldC κ M)) : LaurentSeries κ)} : Set (LaurentSeries κ))) ↥(extendScalars h) := by
    apply FiniteDimensional.of_finrank_pos
    rw [← IntermediateField.relfinrank_eq_finrank_of_le h, ModularCurve.coe_jGeomGen, hrel]
    exact ModularCurve.dedekindPsi_pos M (NeZero.ne M)
  exact finiteDimensional_adjoin_of_extendScalars (ModularCurve.modularFunctionFieldC κ M) (ModularCurve.jGeomGen κ M) h

theorem evalModularPair_eq_eval₂_aeval {R : Type*} [CommRing R] (x y : R) (Φ : Polynomial (Polynomial ℤ)) :
    evalModularPair x y Φ = Φ.eval₂ (Polynomial.aeval (R := ℤ) x).toRingHom y := by
  unfold evalModularPair
  congr 1

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem exists_algEquiv_apply_jGeomGen_eq_and_apply_jNGeomGen_eq
    (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (data : ModularCurve.ModularPolynomialData M)
    (s : ↥(ModularCurve.modularFunctionFieldC k M)) (hs : evalModularPair (ModularCurve.jGeomGen k M) s data.Φ = 0) :
    ∃ ψ : ↥(ModularCurve.modularFunctionFieldC k M) ≃ₐ[k] ↥(ModularCurve.modularFunctionFieldC k M),
      ψ (ModularCurve.jGeomGen k M) = ModularCurve.jGeomGen k M ∧ ψ (ModularCurve.jNGeomGen k M) = s := by
  classical
  have hMk : (M : k) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff k p]; exact hpM
  have hirr := ModularCurve.ModularPolynomialData.irreducible_map_adjoin_jqNModC k M data hMk
  have htr : Transcendental k (ModularCurve.jGeomGen k M) := fun h =>
    (ModularCurve.transcendental_jqModC k) (by
      rw [← ModularCurve.coe_jGeomGen k M]; exact IntermediateField.isAlgebraic_iff.mp h)
  have hy : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (ModularCurve.jGeomGen k M)).toRingHom s = 0 := by
    rw [← evalModularPair_eq_eval₂_aeval]; exact hs
  obtain ⟨ψ₀, ⟨hψj, hψN⟩, -⟩ :=
    ModularCurve.existsUnique_algHom_modularFunctionFieldC_apply_jqModC_eq_of_eval2_eq_zero k M hMk data hirr
      (A := ↥(ModularCurve.modularFunctionFieldC k M)) (ModularCurve.jGeomGen k M) s htr hy

  set T : IntermediateField k ↥(ModularCurve.modularFunctionFieldC k M) :=
    IntermediateField.adjoin k ({ModularCurve.jGeomGen k M} : Set ↥(ModularCurve.modularFunctionFieldC k M)) with hTdef
  have hfixT : ∀ a : ↥T, ψ₀ (a : ↥(ModularCurve.modularFunctionFieldC k M)) = a := by

    let E : IntermediateField k ↥(ModularCurve.modularFunctionFieldC k M) :=
      { toSubalgebra := AlgHom.equalizer ψ₀ (AlgHom.id k _)
        inv_mem' := fun x hx => by
          simp only [Subalgebra.mem_carrier, AlgHom.mem_equalizer, AlgHom.coe_id, id_eq] at hx ⊢
          rw [map_inv₀, hx] }
    have hle : T ≤ E := by
      rw [hTdef, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      show ψ₀ (ModularCurve.jGeomGen k M) = (AlgHom.id k _) (ModularCurve.jGeomGen k M)
      rw [AlgHom.coe_id, id_eq]; exact hψj
    intro a
    have := hle a.2
    first | exact this | simpa [E, AlgHom.mem_equalizer] using this

  haveI : FiniteDimensional ↥T ↥(ModularCurve.modularFunctionFieldC k M) := finiteDimensional_adjoin_jGeomGen k p M hpM
  let L : ↥(ModularCurve.modularFunctionFieldC k M) →ₗ[↥T] ↥(ModularCurve.modularFunctionFieldC k M) :=
    { toFun := ψ₀
      map_add' := map_add ψ₀
      map_smul' := fun a f => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        exact hfixT a }
  have hinj : Function.Injective ψ₀ := ψ₀.toRingHom.injective
  have hsurj : Function.Surjective ψ₀ := by
    have : Function.Surjective L := LinearMap.surjective_of_injective (f := L) hinj
    exact this
  exact ⟨AlgEquiv.ofBijective ψ₀ ⟨hinj, hsurj⟩, hψj, hψN⟩

end B5

open B5 in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (κ k : Type) [Field κ] [CharP κ p] [Field k] [CharP k p] [IsAlgClosed k] [DecidableEq k]
    (τ : κ →+* k)
    (θ θ₀ : ↥(ModularCurve.modularFunctionFieldC κ M) →+* ↥(ModularCurve.modularFunctionFieldC k M))
    (hθκ : ∀ c : κ, θ (algebraMap κ _ c) = algebraMap k _ (τ c))
    (hθ₀κ : ∀ c : κ, θ₀ (algebraMap κ _ c) = algebraMap k _ (τ c))
    (hθj : θ (ModularCurve.jGeomGen κ M) = ModularCurve.jGeomGen k M)
    (hθ₀j : θ₀ (ModularCurve.jGeomGen κ M) = ModularCurve.jGeomGen k M) :
    ∃ α : ↥(ModularCurve.modularFunctionFieldC k M) ≃ₐ[k] ↥(ModularCurve.modularFunctionFieldC k M),
      α (ModularCurve.jGeomGen k M) = ModularCurve.jGeomGen k M ∧ ∀ f, θ f = α (θ₀ f) := by
  classical
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData M

  have heq := ModularCurve.evalModularPair_jGeomGen_eq_zero κ M data
  have ht : evalModularPair (ModularCurve.jGeomGen k M) (θ (ModularCurve.jNGeomGen κ M)) data.Φ = 0 := by
    have := congrArg θ heq
    rwa [map_zero, ModularCurve.map_evalModularPair, hθj] at this
  have ht₀ : evalModularPair (ModularCurve.jGeomGen k M) (θ₀ (ModularCurve.jNGeomGen κ M)) data.Φ = 0 := by
    have := congrArg θ₀ heq
    rwa [map_zero, ModularCurve.map_evalModularPair, hθ₀j] at this
  obtain ⟨ψ, hψj, hψN⟩ := B5.exists_algEquiv_apply_jGeomGen_eq_and_apply_jNGeomGen_eq k p M hpM data _ ht
  obtain ⟨ψ₀, hψ₀j, hψ₀N⟩ := B5.exists_algEquiv_apply_jGeomGen_eq_and_apply_jNGeomGen_eq k p M hpM data _ ht₀
  let α : ↥(ModularCurve.modularFunctionFieldC k M) ≃ₐ[k] ↥(ModularCurve.modularFunctionFieldC k M) := ψ₀.symm.trans ψ
  have hαj : α (ModularCurve.jGeomGen k M) = ModularCurve.jGeomGen k M := by
    show ψ (ψ₀.symm (ModularCurve.jGeomGen k M)) = _
    rw [show ψ₀.symm (ModularCurve.jGeomGen k M) = ModularCurve.jGeomGen k M from (ψ₀.symm_apply_eq).mpr hψ₀j.symm, hψj]
  refine ⟨α, hαj, ?_⟩
  have hext := ModularCurve.ringHom_ext_of_apply_jGeomGen_eq_of_apply_jNGeomGen_eq κ M θ (α.toAlgHom.toRingHom.comp θ₀)
    (fun c => by
      rw [RingHom.comp_apply, hθκ, hθ₀κ]
      show _ = α (algebraMap k _ (τ c))
      rw [AlgEquiv.commutes])
    (by rw [RingHom.comp_apply, hθj, hθ₀j]; exact hαj.symm)
    (by
      rw [RingHom.comp_apply]
      show _ = ψ (ψ₀.symm (θ₀ (ModularCurve.jNGeomGen κ M)))
      rw [show ψ₀.symm (θ₀ (ModularCurve.jNGeomGen κ M)) = ModularCurve.jNGeomGen k M from (ψ₀.symm_apply_eq).mpr hψ₀N.symm, hψN])
  intro f
  exact congrFun (congrArg DFunLike.coe hext) f

end S_ModularCurve_exists_algEquiv_modularFunctionFieldC_apply_jGeomGen_eq_comp
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_modularFunctionFieldC_apply_jGeomGen_eq_comp (solution)
