-- Prove2me | solution 1 for HScattered.Construction.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:09:35.459994+00:00
-- url     : https://prove2.me/submissions/72b1b79f-c812-4d0a-9885-d30e31044d2d

import Mathlib
import Definitions.Def_HScattered_Construction_IsHScattered

set_option autoImplicit false

lemma finrank_sup_span_single {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
    [FiniteDimensional R M] (A : Submodule R M) (v : M) (hv : v ∉ A) :
    Module.finrank R ↥(A ⊔ Submodule.span R {v}) = Module.finrank R A + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ A.zero_mem)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq A (Submodule.span R {v})
  have h2 : A ⊓ Submodule.span R {v} = ⊥ :=
    disjoint_iff.mp ((Submodule.disjoint_span_singleton' hv0).mpr hv)
  rw [h2, finrank_bot, finrank_span_singleton hv0] at h1
  omega

theorem base {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h i : ℕ) (U : Submodule F V) (hh : 1 < h) (hU : HScattered.Bound.IsHScattered F K h U)
    (hi0 : 0 < i) (hih : i < h) :
    HScattered.Bound.IsHScattered F K i U := by
  haveI : Module.Finite F K := Module.Finite.of_finite
  haveI : Module.Finite F V := Module.Finite.trans K V
  obtain ⟨_, hr, hspan, hsc⟩ := hU
  -- one step upward
  have step : ∀ S : Submodule K V, Module.finrank K S < h →
      Module.finrank K S + 1 ≤ Module.finrank F ↥(S.restrictScalars F ⊓ U) →
      ∃ S2 : Submodule K V, Module.finrank K S2 = Module.finrank K S + 1 ∧
        Module.finrank K S2 + 1 ≤ Module.finrank F ↥(S2.restrictScalars F ⊓ U) := by
    intro S hS hSU
    have hne : ¬ (U : Set V) ⊆ (S : Set V) := by
      intro hsub
      have : Submodule.span K (U : Set V) ≤ S := Submodule.span_le.mpr hsub
      rw [hspan] at this
      have h' : S = ⊤ := top_le_iff.mp this
      have : Module.finrank K S = Module.finrank K V := by rw [h']; simp
      omega
    obtain ⟨v, hvU, hvS⟩ := Set.not_subset.mp hne
    refine ⟨S ⊔ Submodule.span K {v}, ?_, ?_⟩
    · exact finrank_sup_span_single S v hvS
    · rw [finrank_sup_span_single S v hvS]
      have hvA : v ∉ S.restrictScalars F ⊓ U := fun hm => hvS hm.1
      have h1 := finrank_sup_span_single (R := F) (S.restrictScalars F ⊓ U) v hvA
      have hle : (S.restrictScalars F ⊓ U) ⊔ Submodule.span F {v} ≤
          (S ⊔ Submodule.span K {v}).restrictScalars F ⊓ U := by
        apply sup_le
        · exact inf_le_inf_right _ (Submodule.restrictScalars_mono F le_sup_left)
        · rw [Submodule.span_singleton_le_iff_mem]
          exact ⟨Submodule.mem_sup_right (Submodule.mem_span_singleton_self v), hvU⟩
      have := Submodule.finrank_mono hle
      omega
  have key : ∀ m : ℕ, ∀ S : Submodule K V, Module.finrank K S + m = h →
      Module.finrank K S + 1 ≤ Module.finrank F ↥(S.restrictScalars F ⊓ U) → False := by
    intro m
    induction m with
    | zero =>
      intro S hS hSU
      have := hsc S (by omega)
      omega
    | succ m ih =>
      intro S hS hSU
      obtain ⟨S2, h1, h2⟩ := step S (by omega) hSU
      exact ih S2 (by omega) h2
  refine ⟨hi0, lt_trans hih hr, hspan, ?_⟩
  intro S hS
  by_contra hcon
  exact key (h - i) S (by omega) (by omega)

theorem solution {F K V : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
    [Fintype F] [Fintype K] [FiniteDimensional K V]
    (h : ℕ) (hh : 1 < h) (U : Submodule F V) (hU : HScattered.Bound.IsHScattered F K h U) :
    (∀ i : ℕ, 0 < i → i < h → HScattered.Bound.IsHScattered F K i U) ∧
      HScattered.Bound.IsHScattered F K 1 U :=
  ⟨fun i hi0 hih => base h i U hh hU hi0 hih, base h 1 U hh hU Nat.one_pos hh⟩
