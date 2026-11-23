-- Prove2me | solution 1 for GlobalTheory.SmGL.SwapBlocks.lower_equiv_upper_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:58.072925+00:00
-- url     : https://prove2.me/submissions/d43a424b-2182-4ce9-aa85-057c19210ae5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_refl
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SmGL_absPow_neg
import Theorems.Thm_GlobalTheory_SmGL_deltaHalf_two
import Theorems.Thm_GlobalTheory_SmGL_mem_parabLower_two
import Theorems.Thm_GlobalTheory_SmGL_mem_parab_two
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRad
import Theorems.Thm_GlobalTheory_SmGL_mem_unipRadLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
namespace GlobalTheory.SmGL.SwapBlocks
section General
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
end General
section Blocks
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n]
end Blocks
section Local
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
end Local
open ValuativeRel MeasureTheory in
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
private theorem nonempty_equiv_smInd_of_eq [TopologicalSpace G] [IsTopologicalGroup G]
    {W : Type} [AddCommGroup W] [Module ℂ W] {H H' : Subgroup G} (h : H = H')
    (σ : Representation ℂ H W) (σ' : Representation ℂ H' W)
    (hσ : ∀ (g : G) (hg : g ∈ H) (hg' : g ∈ H'), σ ⟨g, hg⟩ = σ' ⟨g, hg'⟩) :
    Nonempty ((_root_.GlobalTheory.PRep.smInd H σ).Equiv (_root_.GlobalTheory.PRep.smInd H' σ')) := by
  subst h
  obtain rfl : σ = σ' := MonoidHom.ext fun p => hσ p p.2 p.2
  exact ⟨Representation.Equiv.refl _⟩
open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem parabLower_eq_parab_sumComm (e : a ⊕ b ≃ n) :
    _root_.GlobalTheory.SmGL.parabLower R (_root_.GlobalTheory.SmGL.two e) =
      _root_.GlobalTheory.SmGL.parab R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) := by
  ext g
  rw [_root_.GlobalTheory.SmGL.mem_parabLower_two, _root_.GlobalTheory.SmGL.mem_parab_two]
  simp
open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem leviProj_sumComm_eq_swap_leviProjLower (e : a ⊕ b ≃ n)
    (p : _root_.GlobalTheory.SmGL.parabLower R (_root_.GlobalTheory.SmGL.two e))
    (hp : (p : GL n R) ∈
      _root_.GlobalTheory.SmGL.parab R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e))) :
    _root_.GlobalTheory.SmGL.leviProj R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) ⟨p, hp⟩ =
      _root_.GlobalTheory.SmGL.leviTwo R b a
        ((_root_.GlobalTheory.SmGL.leviTwo R a b).symm
          (_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p)).swap := by
  funext x
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  cases x
  · change _ = ((_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p true : GL b R) :
      Matrix b b R) i j
    rw [_root_.GlobalTheory.SmGL.leviProj_apply, _root_.GlobalTheory.SmGL.leviProjLower_apply]
    rfl
  · change _ = ((_root_.GlobalTheory.SmGL.leviProjLower R (_root_.GlobalTheory.SmGL.two e) p false : GL a R) :
      Matrix a a R) i j
    rw [_root_.GlobalTheory.SmGL.leviProj_apply, _root_.GlobalTheory.SmGL.leviProjLower_apply]
    rfl
open ValuativeRel MeasureTheory in
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
private theorem deltaHalf_inv_leviTwo_eq_deltaHalf_swap (g : GL a k × GL b k) :
    (_root_.GlobalTheory.SmGL.deltaHalf k (_root_.GlobalTheory.SmGL.Two a b))⁻¹ (_root_.GlobalTheory.SmGL.leviTwo k a b g) =
      _root_.GlobalTheory.SmGL.deltaHalf k (_root_.GlobalTheory.SmGL.Two b a) (_root_.GlobalTheory.SmGL.leviTwo k b a g.swap) := by
  rw [MonoidHom.inv_apply, _root_.GlobalTheory.SmGL.deltaHalf_two,
    _root_.GlobalTheory.SmGL.deltaHalf_two, neg_div, neg_div, _root_.GlobalTheory.SmGL.absPow_neg,
    _root_.GlobalTheory.SmGL.absPow_neg]
  simp only [Prod.fst_swap, Prod.snd_swap, MonoidHom.inv_apply, mul_inv, inv_inv]
  exact mul_comm _ _
open ValuativeRel MeasureTheory in
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
private theorem jacquet_apply_eq_of_eq {M M' : Type} [Group M] [Group M']
    (π : Representation ℂ G V) (N : Subgroup G) (s : M →* G) (s' : M' →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ m, s' m ∈ Subgroup.normalizer (N : Set G)) {x : M} {x' : M'} (h : s x = s' x') :
    _root_.GlobalTheory.PRep.jacquet π N s hs x = _root_.GlobalTheory.PRep.jacquet π N s' hs' x' := by
  unfold _root_.GlobalTheory.PRep.jacquet
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  rw [h]
open ValuativeRel MeasureTheory in
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] in
private theorem nonempty_equiv_twist_jacquet_comp {M M' K : Type} [Group M] [Group M'] [Group K]
    (π : Representation ℂ G V) {N N' : Subgroup G} (hN : N = N') (s : M →* G) (s' : M' →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G))
    (hs' : ∀ m, s' m ∈ Subgroup.normalizer (N' : Set G)) (φ : K →* M) (φ' : K →* M')
    (hφ : ∀ x, s (φ x) = s' (φ' x)) (χ : M →* ℂˣ) (χ' : M' →* ℂˣ)
    (hχ : ∀ x, χ (φ x) = χ' (φ' x)) :
    Nonempty (Representation.Equiv
      ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).comp φ)
      ((_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N' s' hs') χ').comp φ')) := by
  subst hN
  have h : (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s hs) χ).comp φ =
      (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.PRep.jacquet π N s' hs') χ').comp φ' := by
    refine MonoidHom.ext fun x => LinearMap.ext fun v => ?_
    simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.twist_apply, hχ,
      jacquet_apply_eq_of_eq π N s s' hs hs' (hφ x)]
  rw [h]
  exact ⟨Representation.Equiv.refl _⟩
open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem unipRadLower_eq_unipRad_sumComm (e : a ⊕ b ≃ n) :
    _root_.GlobalTheory.SmGL.unipRadLower R (_root_.GlobalTheory.SmGL.two e) =
      _root_.GlobalTheory.SmGL.unipRad R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e)) := by
  ext g
  rw [_root_.GlobalTheory.SmGL.mem_unipRadLower, _root_.GlobalTheory.SmGL.mem_unipRad,
    parabLower_eq_parab_sumComm]
  refine and_congr_right fun _ => ?_
  simp only [Bool.forall_bool]
  exact and_comm
open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem leviEmb_leviTwo_apply_eq_fromBlocks (e : a ⊕ b ≃ n) (g : GL a R × GL b R) (u v : a ⊕ b) :
    (_root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two e) (_root_.GlobalTheory.SmGL.leviTwo R a b g) :
        Matrix n n R) (e u) (e v) =
      Matrix.fromBlocks (g.1 : Matrix a a R) 0 0 (g.2 : Matrix b b R) u v := by
  rcases u with u | u <;> rcases v with v | v
  · rw [← _root_.GlobalTheory.SmGL.two_false e u, ← _root_.GlobalTheory.SmGL.two_false e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_same]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_false e u, ← _root_.GlobalTheory.SmGL.two_true e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_ne _ _ _ (by decide : false ≠ true)]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_true e u, ← _root_.GlobalTheory.SmGL.two_false e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_ne _ _ _ (by decide : true ≠ false)]
    rfl
  · rw [← _root_.GlobalTheory.SmGL.two_true e u, ← _root_.GlobalTheory.SmGL.two_true e v,
      _root_.GlobalTheory.SmGL.leviEmb_apply_same]
    rfl
open ValuativeRel MeasureTheory in
variable (R : Type) [CommRing R] {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype n] [DecidableEq n] in
private theorem leviEmb_leviTwo_eq_leviEmb_sumComm_swap (e : a ⊕ b ≃ n) (g : GL a R × GL b R) :
    _root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two e) (_root_.GlobalTheory.SmGL.leviTwo R a b g) =
      _root_.GlobalTheory.SmGL.leviEmb R (_root_.GlobalTheory.SmGL.two ((Equiv.sumComm b a).trans e))
        (_root_.GlobalTheory.SmGL.leviTwo R b a g.swap) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  obtain ⟨u, rfl⟩ := e.surjective i
  obtain ⟨v, rfl⟩ := e.surjective j
  have hu : e u = ((Equiv.sumComm b a).trans e) u.swap := by simp
  have hv : e v = ((Equiv.sumComm b a).trans e) v.swap := by simp
  rw [leviEmb_leviTwo_apply_eq_fromBlocks, hu, hv, leviEmb_leviTwo_apply_eq_fromBlocks]
  rcases u with u | u <;> rcases v with v | v <;> rfl
end GlobalTheory.SmGL.SwapBlocks
end
end

set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.SwapBlocks
open ValuativeRel MeasureTheory
namespace GlobalTheory.SmGL.SwapBlocks
namespace _root_.GlobalTheory.SmGL.SwapBlocks
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n] (e : a ⊕ b ≃ n) (V : Type) [AddCommGroup V] [Module ℂ V], (∀ ρ : Representation ℂ (GL a k × GL b k) V, Nonempty ((_root_.GlobalTheory.SmGL.ind₂Lower e ρ).Equiv (_root_.GlobalTheory.SmGL.ind₂ ((Equiv.sumComm b a).trans e) (ρ.comp (MulEquiv.prodComm : GL b k × GL a k ≃* GL a k × GL b k).toMonoidHom)))) ∧ ∀ π : Representation ℂ (GL n k) V, Nonempty ((_root_.GlobalTheory.SmGL.jac₂Lower e π).Equiv ((_root_.GlobalTheory.SmGL.jac₂ ((Equiv.sumComm b a).trans e) π).comp (MulEquiv.prodComm : GL a k × GL b k ≃* GL b k × GL a k).toMonoidHom)) := by
  intro k _ _ _ _ a b n _ _ _ _ _ _ e V _ _
  refine ⟨fun ρ => ?_, fun π => ?_⟩
  · unfold _root_.GlobalTheory.SmGL.ind₂Lower _root_.GlobalTheory.SmGL.ind₂
      _root_.GlobalTheory.SmGL.parIndLower _root_.GlobalTheory.SmGL.parInd
    refine nonempty_equiv_smInd_of_eq (parabLower_eq_parab_sumComm k e) _ _
      fun g hg hg' => LinearMap.ext fun v => ?_
    simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.twist_apply,
      MulEquiv.coe_toMonoidHom]
    rw [leviProj_sumComm_eq_swap_leviProjLower k e ⟨g, hg⟩ hg', ← deltaHalf_inv_leviTwo_eq_deltaHalf_swap]
    simp
  · unfold _root_.GlobalTheory.SmGL.jac₂Lower _root_.GlobalTheory.SmGL.jac₂ _root_.GlobalTheory.SmGL.jacLower
      _root_.GlobalTheory.SmGL.jac _root_.GlobalTheory.SmGL.jacU
    rw [MonoidHom.comp_assoc]
    refine nonempty_equiv_twist_jacquet_comp π (unipRadLower_eq_unipRad_sumComm k e) _ _ _ _
      _ _ (fun x => leviEmb_leviTwo_eq_leviEmb_sumComm_swap k e x) _ _ fun x => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [MonoidHom.inv_apply, show (MulEquiv.prodComm x : GL b k × GL a k) = x.swap from rfl,
      ← deltaHalf_inv_leviTwo_eq_deltaHalf_swap, MonoidHom.inv_apply, inv_inv]
end _root_.GlobalTheory.SmGL.SwapBlocks
end GlobalTheory.SmGL.SwapBlocks
