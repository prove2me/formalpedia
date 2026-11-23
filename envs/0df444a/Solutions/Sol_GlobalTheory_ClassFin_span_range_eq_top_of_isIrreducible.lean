-- Prove2me | solution 1 for GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:58.151801+00:00
-- url     : https://prove2.me/submissions/829a41e1-b1a1-455d-860a-5e94cd32ef75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SpanRangeEqTopOfIsIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
namespace GlobalTheory.ClassFin
open scoped MonoidAlgebra
open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
open scoped MonoidAlgebra in
private theorem subalgebra_end_eq_whole_of_isSimpleModule {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (A : Subalgebra ℂ (Module.End ℂ V)) [IsSimpleModule A V] :
    A = ⊤ := by
  classical
  have schur : ∀ f : V →ₗ[A] V, ∃ c : ℂ, ∀ y, f y = c • y := by
    intro f
    obtain ⟨c, hc⟩ := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := V) ℂ).2 f
    exact ⟨c, fun y => by rw [← hc]; rfl⟩
  let b := Module.finBasis ℂ V
  let ι := Fin (Module.finrank ℂ V)
  let N : Submodule A (ι → V) := Submodule.span A {fun i => b i}
  obtain ⟨W, hW⟩ := exists_isCompl N
  let P : (ι → V) →ₗ[A] (ι → V) := N.subtype.comp (Submodule.linearProjOfIsCompl N W hW)
  have hPN : ∀ x, P x ∈ N := fun x => (Submodule.linearProjOfIsCompl N W hW x).2
  have hPfix : ∀ x ∈ N, P x = x := fun x hx => by
    simp only [P, LinearMap.comp_apply, Submodule.subtype_apply]
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hW ⟨x, hx⟩)
  have hcomm : ∀ (T : Module.End ℂ V) (x : ι → V), P (fun i => T (x i)) = fun i => T (P x i) := by
    intro T x
    have hsingle : ∀ (i j : ι) (y : V), P (Pi.single j (T y)) i = T (P (Pi.single j y) i) := by
      intro i j y
      obtain ⟨c, hc⟩ := schur ((LinearMap.proj i).comp (P.comp (LinearMap.single A (fun _ : ι => V) j)))
      have h1 := hc (T y)
      have h2 := hc y
      simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply] at h1 h2
      rw [h1, h2, map_smul]
    funext i
    conv_lhs => rw [← Finset.univ_sum_single (fun i => T (x i)), map_sum]
    conv_rhs => rw [← Finset.univ_sum_single x, map_sum]
    simp only [Finset.sum_apply, map_sum, hsingle]
  ext T
  simp only [Algebra.mem_top, iff_true]
  have hmem : (fun i => T (b i)) ∈ N := by
    have hfix : P (fun i => T (b i)) = fun i => T (b i) := by
      rw [hcomm T (fun i => b i), hPfix _ (Submodule.mem_span_singleton_self _)]
    rw [← hfix]
    exact hPN _
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
  have hT : T = (a : Module.End ℂ V) := by
    refine b.ext fun i => ?_
    have := congrFun ha i
    exact this.symm
  rw [hT]
  exact a.2
end GlobalTheory.ClassFin
end

set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin
open scoped MonoidAlgebra
open Matrix
open scoped Kronecker ComplexOrder TensorProduct
open scoped MonoidAlgebra
namespace GlobalTheory.ClassFin
namespace _root_.GlobalTheory.ClassFin
theorem _root_.solution :
    ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) [FiniteDimensional ℂ V], ρ.IsIrreducible → Submodule.span ℂ (Set.range ρ) = ⊤ := by
  intro G _ V _ _ ρ _ h
  let A : Subalgebra ℂ (Module.End ℂ V) := Algebra.adjoin ℂ (Set.range ρ)
  have hρA : ∀ g, ρ g ∈ A := fun g => Algebra.subset_adjoin ⟨g, rfl⟩
  have hspan : Subalgebra.toSubmodule A = Submodule.span ℂ (Set.range ρ) := by
    rw [Algebra.adjoin_eq_span]
    congr 1
    have : Set.range ρ = ((MonoidHom.mrange ρ : Submonoid (Module.End ℂ V)) : Set (Module.End ℂ V)) :=
      (MonoidHom.coe_mrange ρ).symm
    rw [this, Submonoid.closure_eq]
  let φ : Submodule A V → Subrepresentation ρ := fun M =>
    ⟨M.restrictScalars ℂ, fun g v hv => M.smul_mem (⟨ρ g, hρA g⟩ : A) hv⟩
  haveI : IsSimpleModule A V := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun M => ?_ }
    · obtain ⟨S, S', hS'⟩ := h.exists_pair_ne
      have hzero : ∀ x : V, x = 0 := fun x => by
        have : x ∈ (⊤ : Submodule A V) := Submodule.mem_top
        rw [← hbt] at this
        exact (Submodule.mem_bot A).1 this
      have hall : ∀ T U : Subrepresentation ρ, T = U := fun T U => by
        apply Subrepresentation.ext
        ext x
        rw [hzero x]
        exact ⟨fun _ => U.toSubmodule.zero_mem, fun _ => T.toSubmodule.zero_mem⟩
      exact hS' (hall S S')
    · rcases h.eq_bot_or_eq_top (φ M) with hM | hM
      · left
        have := congrArg Subrepresentation.toSubmodule hM
        exact (Submodule.restrictScalars_eq_bot_iff ℂ A V).1 this
      · right
        have := congrArg Subrepresentation.toSubmodule hM
        exact (Submodule.restrictScalars_eq_top_iff ℂ A V).1 this
  rw [← hspan, subalgebra_end_eq_whole_of_isSimpleModule A]
  ext x
  simp
end _root_.GlobalTheory.ClassFin
end GlobalTheory.ClassFin
