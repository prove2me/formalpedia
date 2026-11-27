-- Prove2me | solution 1 for GlobalTheory.IsoSep.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:34:56.717966+00:00
-- url     : https://prove2.me/submissions/ac088cb7-e4fb-4e72-a2ea-b713e9c0ec6e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntertwiningMapNeZeroOfIsotypicIrreducible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IsoSep
open Representation
namespace GlobalTheory.IsoSep
theorem _root_.solution : ∀ (H V W : Type) [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H V) (σ : Representation ℂ H W), σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ → (∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ H W'), σ'.IsIrreducible → ∀ f' : σ'.IntertwiningMap ρ, f' ≠ 0 → Nonempty (σ.Equiv σ')) → ∀ v : V, v ≠ 0 → ∃ p : ρ.IntertwiningMap σ, p v ≠ 0 := by
  intro H V W _ _ _ _ _ ρ σ hσ hsum hiso v hv
  haveI := hσ
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)

  have hatom : ∀ f : σ.IntertwiningMap ρ, f ≠ 0 → IsAtom f.range := by
    intro f hf
    refine ⟨?_, ?_⟩
    · intro h
      apply hf
      ext w
      have hw : f w ∈ f.range := ⟨w, rfl⟩
      rw [h] at hw
      exact hw
    · intro U hU
      let U' : Subrepresentation σ := ⟨U.toSubmodule.comap f.toLinearMap, fun g w hw => by
        show f (σ g w) ∈ U.toSubmodule
        rw [f.isIntertwining]
        exact U.apply_mem_toSubmodule g hw⟩
      rcases eq_bot_or_eq_top U' with h | h
      · refine le_antisymm (fun x hx => ?_) bot_le
        obtain ⟨w, rfl⟩ := hU.le hx
        have hw : w ∈ U'.toSubmodule := hx
        rw [h] at hw
        have hw0 : w = 0 := (Submodule.mem_bot ℂ).1 hw
        show f w ∈ (⊥ : Submodule ℂ V)
        rw [hw0, map_zero]
        exact zero_mem _
      · exfalso
        refine hU.ne (le_antisymm hU.le ?_)
        rintro _ ⟨w, rfl⟩
        have hw : w ∈ U'.toSubmodule := by rw [h]; trivial
        exact hw

  have hss : IsSemisimpleModule (MonoidAlgebra ℂ H) ρ.asModule := by
    apply IsSemisimpleModule.of_sSup_simples_eq_top
    refine eq_top_iff.2 fun x _ => ?_
    have hx : ρ.asModuleEquiv x ∈ (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) := by
      rw [hsum]; trivial
    have key := Submodule.iSup_induction _ (motive := fun y : V => ρ.asModuleEquiv.symm y ∈
      sSup {m : Submodule (MonoidAlgebra ℂ H) ρ.asModule | IsSimpleModule (MonoidAlgebra ℂ H) m}) hx
      (fun f y hy => by
        by_cases hf : f = 0
        · subst hf
          obtain ⟨w, rfl⟩ := hy
          simp
        · refine le_sSup (a := e f.range) ?_ ?_
          · exact isSimpleModule_iff_isAtom.2 ((e.isAtom_iff _).2 (hatom f hf))
          · exact hy)
      (by simp) (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    simpa using key

  let K : Submodule (MonoidAlgebra ℂ H) ρ.asModule := Submodule.span _ {ρ.asModuleEquiv.symm v}
  have hK : K ≠ ⊥ := by
    intro h
    apply hv
    have hm : ρ.asModuleEquiv.symm v ∈ K := Submodule.subset_span rfl
    rw [h, Submodule.mem_bot] at hm
    simpa using hm
  obtain ⟨N, hN, hNK⟩ := (eq_bot_or_exists_atom_le K).resolve_left hK
  obtain ⟨C, hC⟩ := exists_isCompl N
  let N' := e.symm N
  let C' := e.symm C
  have hC' : IsCompl N' C' := (e.isCompl_iff).2 (by
    simp only [N', C', OrderIso.apply_symm_apply]; exact hC)
  have hN' : IsAtom N' := (e.isAtom_iff N').1 (by simp only [N', OrderIso.apply_symm_apply]; exact hN)
  have hc : IsCompl N'.toSubmodule C'.toSubmodule := by
    constructor
    · rw [disjoint_iff]; exact congrArg Subrepresentation.toSubmodule hC'.inf_eq_bot
    · rw [codisjoint_iff]; exact congrArg Subrepresentation.toSubmodule hC'.sup_eq_top
  let P := Submodule.projectionOnto N'.toSubmodule C'.toSubmodule hc
  let τ := N'.toRepresentation
  let p : ρ.IntertwiningMap τ := ⟨P, fun g => LinearMap.ext fun x => by
    have hx : x ∈ N'.toSubmodule ⊔ C'.toSubmodule := by rw [hc.sup_eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 : P (ρ g y) = ⟨ρ g y, N'.apply_mem_toSubmodule g hy⟩ :=
      Submodule.projectionOnto_apply_left hc ⟨ρ g y, N'.apply_mem_toSubmodule g hy⟩
    have h2 : P (ρ g z) = 0 :=
      Submodule.projectionOnto_apply_right hc ⟨ρ g z, C'.apply_mem_toSubmodule g hz⟩
    have h3 : P y = ⟨y, hy⟩ := Submodule.projectionOnto_apply_left hc ⟨y, hy⟩
    have h4 : P z = 0 := Submodule.projectionOnto_apply_right hc ⟨z, hz⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, map_add, h1, h2, h3, h4, add_zero, map_zero]
    rfl⟩
  have hpv : p v ≠ 0 := by
    intro h0
    have hvC : v ∈ C'.toSubmodule := (Submodule.projectionOnto_apply_eq_zero_iff hc).1 h0
    have hKC : K ≤ C := by
      refine Submodule.span_le.2 ?_
      rintro _ rfl
      exact hvC
    have hNC : N ≤ N ⊓ C := le_inf le_rfl (hNK.trans hKC)
    rw [hC.inf_eq_bot] at hNC
    exact hN.1 (le_bot_iff.1 hNC)

  have hN'0 : N'.toSubmodule ≠ ⊥ := fun h => hN'.1 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨x0, hx0, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN'0
  have hτ : τ.IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
    · have hm : (⟨x0, hx0⟩ : N'.toSubmodule) ∈ (⊤ : Subrepresentation τ).toSubmodule := trivial
      rw [← h] at hm
      have : (⟨x0, hx0⟩ : N'.toSubmodule) = 0 := (Submodule.mem_bot ℂ).1 hm
      exact hx00 (congrArg Subtype.val this)
    · let U'' : Subrepresentation ρ := ⟨U.toSubmodule.map N'.toSubmodule.subtype, fun g x hx => by
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨τ g y, U.apply_mem_toSubmodule g hy, rfl⟩⟩
      have hle : U'' ≤ N' := by
        rintro _ ⟨y, -, rfl⟩
        exact y.2
      rcases hN'.le_iff.1 hle with h | h
      · left
        refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun y hy => ?_)
        have hm : (y : V) ∈ U''.toSubmodule := ⟨y, hy, rfl⟩
        rw [h] at hm
        have h0 : (y : V) = 0 := (Submodule.mem_bot ℂ).1 hm
        exact (Submodule.mem_bot ℂ).2 (Subtype.ext h0)
      · right
        refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun y _ => ?_)
        have hm : (y : V) ∈ U''.toSubmodule := by rw [h]; exact y.2
        obtain ⟨z, hz, hzy⟩ := hm
        have : z = y := Subtype.ext hzy
        rw [← this]
        exact hz
  let f' : τ.IntertwiningMap ρ := ⟨N'.toSubmodule.subtype, fun g => LinearMap.ext fun x => rfl⟩
  have hf' : f' ≠ 0 := by
    intro h
    have := congrArg (fun q : τ.IntertwiningMap ρ => q ⟨x0, hx0⟩) h
    exact hx00 this
  obtain ⟨eqv⟩ := hiso _ τ hτ f' hf'
  refine ⟨eqv.symm.toIntertwiningMap.comp p, fun h => hpv ?_⟩
  have := congrArg eqv h
  simpa using this
end GlobalTheory.IsoSep
