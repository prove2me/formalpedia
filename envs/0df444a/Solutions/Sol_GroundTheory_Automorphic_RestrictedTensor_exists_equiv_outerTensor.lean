-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.exists_equiv_outerTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:08.769181+00:00
-- url     : https://prove2.me/submissions/3f22d28c-7083-456d-a29c-d87a53a4fb5c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Existence
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_OuterTensor
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TwoFactor
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_prodRep_apply
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_tensorForm_tmul
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_commute_adjoin
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_eq_zero_of_place
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_exists_rankOne_simple
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isIrreducible_mGenQuotRep
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isIrreducible_outerTensor
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isSimpleUnder_winOps
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mGenQuotForm_apply
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_outerTensor_tmul
import Theorems.Thm_P2M_GroundTheory_Automorphic_RestrictedTensor_nonempty_equiv_of_matrixCoeff_eq__99399df656ad


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set TensorProduct
open scoped TensorProduct
variable {M₁ M₂ : Type*} [Monoid M₁] [Monoid M₂] {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {ρ₁ : Representation ℂ M₁ V} {ρ₂ : Representation ℂ M₂ V}
  {hcomm : ∀ a b, ρ₁ a * ρ₂ b = ρ₂ b * ρ₁ a} {e₁ e₂ : End ℂ V}
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (hirr : (prodRep ρ₁ ρ₂ hcomm).IsIrreducible)
    (he₁ : IsWinProj ρ₁ e₁) (he₂ : IsWinProj ρ₂ e₂) (he₁₂ : ∀ b, e₁ * ρ₂ b = ρ₂ b * e₁)
    (he₂₁ : ∀ a, e₂ * ρ₁ a = ρ₁ a * e₂) (hee : e₁ * e₂ = e₂ * e₁)
    [FiniteDimensional ℂ (LinearMap.range (e₁ * e₂))] (hne : LinearMap.range (e₁ * e₂) ≠ ⊥) :
    ∃ (N₁ N₂ : Submodule ℂ V), N₁ ≤ LinearMap.range (e₁ * e₂) ∧ N₂ ≤ LinearMap.range (e₁ * e₂) ∧
      N₁ ≠ ⊥ ∧ N₂ ≠ ⊥ ∧ (∀ a, ∀ n ∈ N₁, e₁ (ρ₁ a n) ∈ N₁) ∧ (∀ b, ∀ n ∈ N₂, e₂ (ρ₂ b n) ∈ N₂) ∧
      (mGenQuotRep ρ₁ e₁ N₁).IsIrreducible ∧ (mGenQuotRep ρ₂ e₂ N₂).IsIrreducible ∧
      ((∀ T : End ℂ ((mGenSubrep ρ₂ N₂).toSubmodule ⧸ mGenKernel ρ₂ e₂ N₂),
          (∀ b, T * mGenQuotRep ρ₂ e₂ N₂ b = mGenQuotRep ρ₂ e₂ N₂ b * T) → ∃ c : ℂ, T = c • 1) →
        Nonempty ((prodRep ρ₁ ρ₂ hcomm).Equiv
          (outerTensor (mGenQuotRep ρ₁ e₁ N₁) (mGenQuotRep ρ₂ e₂ N₂)))) := by
  classical
  haveI := hirr
  set P := prodRep ρ₁ ρ₂ hcomm
  set W := LinearMap.range (e₁ * e₂)
  have hE1 : ∀ w ∈ W, e₁ w = w := by
    rintro _ ⟨x, rfl⟩
    show e₁ (e₁ (e₂ x)) = e₁ (e₂ x)
    exact he₁.idem _
  have hE2 : ∀ w ∈ W, e₂ w = w := by
    rintro _ ⟨x, rfl⟩
    show e₂ (e₁ (e₂ x)) = e₁ (e₂ x)
    rw [← Module.End.mul_apply e₂ e₁, ← hee, Module.End.mul_apply, he₂.idem]
  have hEw : ∀ w ∈ W, (e₁ * e₂) w = w := fun w hw => by
    show e₁ (e₂ w) = w
    rw [hE2 w hw, hE1 w hw]
  have hEidem : ∀ v, (e₁ * e₂) ((e₁ * e₂) v) = (e₁ * e₂) v := fun v => hEw _ ⟨v, rfl⟩

  let sub₁ : Subrepresentation P → Subrepresentation ρ₁ := fun Y =>
    ⟨Y.toSubmodule, fun a y hy => by
      have := Y.apply_mem_toSubmodule (a, 1) hy
      simpa [P, prodRep_apply] using this⟩
  let sub₂ : Subrepresentation P → Subrepresentation ρ₂ := fun Y =>
    ⟨Y.toSubmodule, fun b y hy => by
      have := Y.apply_mem_toSubmodule (1, b) hy
      simpa [P, prodRep_apply] using this⟩
  have hE : IsWinProj P (e₁ * e₂) :=
    ⟨hEidem, fun Y y hy => he₁.mem (sub₁ Y) _ (he₂.mem (sub₂ Y) _ hy)⟩

  let T₁ : M₁ → End ℂ W := fun a => winOp P (e₁ * e₂) (a, 1)
  let T₂ : M₂ → End ℂ W := fun b => winOp P (e₁ * e₂) (1, b)
  have hT₁ : ∀ a (w : W), (T₁ a w : V) = e₁ (ρ₁ a w) := fun a w => by
    show e₁ (e₂ (ρ₁ a (ρ₂ 1 w))) = _
    rw [map_one, Module.End.one_apply, ← Module.End.mul_apply e₂, he₂₁, Module.End.mul_apply,
      hE2 _ w.2]
  have hT₂ : ∀ b (w : W), (T₂ b w : V) = e₂ (ρ₂ b w) := fun b w => by
    show e₁ (e₂ (ρ₁ 1 (ρ₂ b w))) = _
    rw [map_one, Module.End.one_apply, ← Module.End.mul_apply e₁ e₂, hee, Module.End.mul_apply,
      ← Module.End.mul_apply e₁ (ρ₂ b), he₁₂, Module.End.mul_apply, hE1 _ w.2]
  have hT₁₂ : ∀ a b, T₁ a * T₂ b = winOp P (e₁ * e₂) (a, b) := fun a b => by
    ext w
    show (T₁ a (T₂ b w) : V) = e₁ (e₂ (ρ₁ a (ρ₂ b w)))
    rw [hT₁, hT₂, ← Module.End.mul_apply e₂ (ρ₁ a), he₂₁, Module.End.mul_apply]
  have hT₂₁ : ∀ a b, T₂ b * T₁ a = winOp P (e₁ * e₂) (a, b) := fun a b => by
    ext w
    show (T₂ b (T₁ a w) : V) = e₁ (e₂ (ρ₁ a (ρ₂ b w)))
    rw [hT₂, hT₁]
    show e₂ (ρ₂ b (e₁ (ρ₁ a w))) = e₁ (e₂ (ρ₁ a (ρ₂ b w)))
    rw [← Module.End.mul_apply (ρ₂ b) e₁, ← he₁₂, Module.End.mul_apply,
      ← Module.End.mul_apply e₂ e₁, ← hee, Module.End.mul_apply,
      ← Module.End.mul_apply (ρ₂ b) (ρ₁ a), ← hcomm, Module.End.mul_apply]
  set Tp : Bool → Set (End ℂ W) := fun i => if i then range T₁ else range T₂
  have hcommTp : ∀ i j, i ≠ j → ∀ s ∈ Tp i, ∀ t ∈ Tp j, Commute s t := by
    intro i j hij s hs t ht
    cases i <;> cases j <;> simp only [Tp, if_true, if_false] at hs ht
    · exact absurd rfl hij
    · obtain ⟨b, rfl⟩ := hs
      obtain ⟨a, rfl⟩ := ht
      exact (hT₂₁ a b).trans (hT₁₂ a b).symm
    · obtain ⟨a, rfl⟩ := hs
      obtain ⟨b, rfl⟩ := ht
      exact (hT₁₂ a b).trans (hT₂₁ a b).symm
    · exact absurd rfl hij
  have hsimple : IsSimpleUnder (⋃ i, Tp i) := by
    have h0 := isSimpleUnder_winOps hE hne
    refine ⟨h0.1, fun p hp => h0.2 p ?_⟩
    rintro _ ⟨⟨a, b⟩, rfl⟩
    have hmem : winOp P (e₁ * e₂) (a, b) ∈ Algebra.adjoin ℂ (⋃ i, Tp i) := by
      rw [← hT₁₂]
      refine Subalgebra.mul_mem _ (Algebra.subset_adjoin ?_) (Algebra.subset_adjoin ?_)
      · exact mem_iUnion.2 ⟨true, by simp [Tp]⟩
      · exact mem_iUnion.2 ⟨false, by simp [Tp]⟩
    exact IsStable.adjoin hp _ hmem
  have hvanish := fun i (N : Submodule ℂ W) (hN : N ≠ ⊥) (hNs : IsStable (Tp i) N)
      (a : End ℂ W) (ha : a ∈ Algebra.adjoin ℂ (Tp i)) (h0 : ∀ x ∈ N, a x = 0) =>
    eq_zero_of_place hsimple hcommTp i hN hNs ha h0
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hne
  have hdata := fun i => exists_rankOne_simple (Tp i)
  choose N hNst hN0 hNsimple p hp n hnN hn0 hpn hpN using hdata
  have hpp : ∀ i, p i * p i = p i := by
    intro i
    rw [← sub_eq_zero]
    refine hvanish i (N i) (hN0 i) (hNst i) _ (Subalgebra.sub_mem _
      (Subalgebra.mul_mem _ (hp i) (hp i)) (hp i)) fun x hx => ?_
    obtain ⟨d, hd⟩ := hpN i x hx
    rw [LinearMap.sub_apply, Module.End.mul_apply, hd, map_smul, hpn i, sub_self]
  have hcex : ∀ i, ∀ t ∈ Tp i, ∃ c : ℂ, p i (t (n i)) = c • n i :=
    fun i t ht => hpN i _ (hNst i t ht (n i) (hnN i))
  have hTpT : ∀ i, ∀ t ∈ Tp i, ∀ c : ℂ, p i (t (n i)) = c • n i → p i * t * p i = c • p i := by
    intro i t ht c hc
    rw [← sub_eq_zero]
    refine hvanish i (N i) (hN0 i) (hNst i) _ (Subalgebra.sub_mem _ (Subalgebra.mul_mem _
      (Subalgebra.mul_mem _ (hp i) (Algebra.subset_adjoin ht)) (hp i))
      (Subalgebra.smul_mem _ (hp i) _)) fun y hy => ?_
    obtain ⟨d, hd⟩ := hpN i y hy
    rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hd, map_smul, map_smul,
      hc, LinearMap.smul_apply, hd, smul_comm, sub_self]
  have hcommp : Commute (p true) (p false) :=
    commute_adjoin hcommTp (by decide) (hp true) (hp false)
  have hT₁mem : ∀ a, T₁ a ∈ Tp true := fun a => by simp [Tp]
  have hT₂mem : ∀ b, T₂ b ∈ Tp false := fun b => by simp [Tp]
  choose c₁ hc₁ using fun a => hcex true (T₁ a) (hT₁mem a)
  choose c₂ hc₂ using fun b => hcex false (T₂ b) (hT₂mem b)
  have hT₁one : T₁ 1 = 1 := by
    ext w
    rw [hT₁, map_one, Module.End.one_apply, hE1 _ w.2]
    rfl
  have hT₂one : T₂ 1 = 1 := by
    ext w
    rw [hT₂, map_one, Module.End.one_apply, hE2 _ w.2]
    rfl
  have hc₁one : c₁ 1 = 1 := by
    have h1 := hc₁ 1
    rw [hT₁one, Module.End.one_apply, hpn] at h1
    have h2 : (c₁ 1 - 1) • n true = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h (hn0 true)
  have hc₂one : c₂ 1 = 1 := by
    have h1 := hc₂ 1
    rw [hT₂one, Module.End.one_apply, hpn] at h1
    have h2 : (c₂ 1 - 1) • n false = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h (hn0 false)

  obtain ⟨x₁, hx₁⟩ : ∃ y ∈ (⊤ : Submodule ℂ W), p true y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := hvanish true ⊤ top_ne_bot (fun _ _ _ _ => trivial) (p true) (hp true)
      fun x _ => hcon x trivial
    apply hn0 true
    rw [← hpn true, this, LinearMap.zero_apply]
  set y₁ := p true x₁
  have hy₁ : p true y₁ = y₁ := by
    show p true (p true x₁) = p true x₁
    rw [← Module.End.mul_apply, hpp]
  let Y : Submodule ℂ W := LinearMap.ker (p true - 1)
  have hY : y₁ ∈ Y := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hy₁, Module.End.one_apply, sub_self]
  have hY0 : Y ≠ ⊥ := fun h => hx₁.2 (by
    have : y₁ ∈ (⊥ : Submodule ℂ W) := h ▸ hY
    simpa using this)
  have hYs : IsStable (Tp false) Y := by
    intro t ht y hy
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hy ⊢
    have hct : Commute (p true) t :=
      commute_adjoin hcommTp (by decide) (hp true) (Algebra.subset_adjoin ht)
    rw [← Module.End.mul_apply, hct.eq, Module.End.mul_apply, hy]
  obtain ⟨y₂, hy₂Y, hy₂⟩ : ∃ y ∈ Y, p false y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := hvanish false Y hY0 hYs (p false) (hp false) hcon
    apply hn0 false
    rw [← hpn false, this, LinearMap.zero_apply]
  set xs := p false y₂
  have hxs0 : xs ≠ 0 := hy₂
  have hxs2 : p false xs = xs := by
    show p false (p false y₂) = p false y₂
    rw [← Module.End.mul_apply, hpp]
  have hxs1 : p true xs = xs := by
    have h := hy₂Y
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    show p true (p false y₂) = p false y₂
    rw [← Module.End.mul_apply, hcommp.eq, Module.End.mul_apply, h]
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ : Dual ℂ W, φ xs ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hxs0 ((Module.forall_dual_apply_eq_zero_iff ℂ xs).1 hcon)
  set φ : Dual ℂ W := (φ₀ xs)⁻¹ • (φ₀ ∘ₗ p true ∘ₗ p false)
  have hφ1 : φ xs = 1 := by
    simp [φ, hxs2, hxs1, hφ₀]
  have hφp1 : ∀ w, φ (p true w) = φ w := fun w => by
    simp only [φ, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [← Module.End.mul_apply (p false), ← hcommp.eq, Module.End.mul_apply,
      ← Module.End.mul_apply (p true) (p true), hpp]
  have hφp2 : ∀ w, φ (p false w) = φ w := fun w => by
    simp only [φ, LinearMap.smul_apply, LinearMap.comp_apply]
    rw [← Module.End.mul_apply (p false) (p false), hpp]

  have hcoefV : ∀ a b, φ (winOp P (e₁ * e₂) (a, b) xs) = c₁ a * c₂ b := by
    intro a b
    rw [← hT₁₂, Module.End.mul_apply]
    set z := T₂ b xs
    have hz1 : p true z = z := by
      have hct : Commute (p true) (T₂ b) :=
        commute_adjoin hcommTp (by decide) (hp true) (Algebra.subset_adjoin (hT₂mem b))
      show p true (T₂ b xs) = T₂ b xs
      rw [← Module.End.mul_apply, hct.eq, Module.End.mul_apply, hxs1]
    have h1 : φ (T₁ a z) = c₁ a * φ z := by
      rw [← hφp1, ← hz1]
      have := congrArg (fun F : End ℂ W => φ (F z)) (hTpT true (T₁ a) (hT₁mem a) (c₁ a) (hc₁ a))
      simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul, smul_eq_mul] at this
      rw [this, hz1]
    have h2 : φ z = c₂ b := by
      rw [← hφp2]
      have := congrArg (fun F : End ℂ W => φ (F xs)) (hTpT false (T₂ b) (hT₂mem b) (c₂ b) (hc₂ b))
      simp only [Module.End.mul_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, hxs2] at this
      rw [this, hφ1, mul_one]
    rw [h1, h2]

  set N₁ : Submodule ℂ V := (N true).map W.subtype
  set N₂ : Submodule ℂ V := (N false).map W.subtype
  have hN₁W : N₁ ≤ W := by rintro _ ⟨w, -, rfl⟩; exact w.2
  have hN₂W : N₂ ≤ W := by rintro _ ⟨w, -, rfl⟩; exact w.2
  have hN₁e : N₁ ≤ LinearMap.range e₁ := fun x hx => ⟨x, hE1 x (hN₁W hx)⟩
  have hN₂e : N₂ ≤ LinearMap.range e₂ := fun x hx => ⟨x, hE2 x (hN₂W hx)⟩
  have hN₁st : ∀ a, ∀ x ∈ N₁, e₁ (ρ₁ a x) ∈ N₁ := by
    rintro a _ ⟨w, hw, rfl⟩
    exact ⟨T₁ a w, hNst true _ (hT₁mem a) w hw, hT₁ a w⟩
  have hN₂st : ∀ b, ∀ x ∈ N₂, e₂ (ρ₂ b x) ∈ N₂ := by
    rintro b _ ⟨w, hw, rfl⟩
    exact ⟨T₂ b w, hNst false _ (hT₂mem b) w hw, hT₂ b w⟩
  have hN₁0 : N₁ ≠ ⊥ := fun h => hn0 true (by
    have : ((n true : W) : V) ∈ N₁ := ⟨n true, hnN true, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this)
  have hN₂0 : N₂ ≠ ⊥ := fun h => hn0 false (by
    have : ((n false : W) : V) ∈ N₂ := ⟨n false, hnN false, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this)
  have hmin : ∀ i (M' : Submodule ℂ V), (∀ t ∈ Tp i, ∀ w : W, (w : V) ∈ M' → (t w : V) ∈ M') →
      M' ≤ (N i).map W.subtype → M' ≠ ⊥ → M' = (N i).map W.subtype := by
    intro i M' hst hle hne'
    set q : Submodule ℂ (N i) := (M'.comap W.subtype).comap (N i).subtype
    have hq : IsStable (restrictSet (Tp i) (N i) (hNst i)) q := by
      rintro _ ⟨⟨t, ht⟩, rfl⟩ y hy
      exact hst t ht y hy
    have hq0 : q ≠ ⊥ := by
      obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne'
      obtain ⟨m, hm, rfl⟩ := hle hu
      intro h
      have : (⟨m, hm⟩ : N i) ∈ q := hu
      rw [h, Submodule.mem_bot] at this
      have hm0 : m = 0 := congrArg Subtype.val this
      exact hu0 (by simp [hm0])
    have hqt := ((hNsimple i).2 q hq).resolve_left hq0
    refine le_antisymm hle ?_
    rintro _ ⟨m, hm, rfl⟩
    have : (⟨m, hm⟩ : N i) ∈ q := hqt ▸ Submodule.mem_top
    exact this
  have hN₁min : ∀ N' : Submodule ℂ V, N' ≤ N₁ → N' ≠ ⊥ → (∀ a, ∀ x ∈ N', e₁ (ρ₁ a x) ∈ N') →
      N' = N₁ := fun N' hle hne' hst => hmin true N' (fun t ht w hw => by
        simp only [Tp, if_true] at ht
        obtain ⟨a, rfl⟩ := ht
        rw [hT₁]
        exact hst a w hw) hle hne'
  have hN₂min : ∀ N' : Submodule ℂ V, N' ≤ N₂ → N' ≠ ⊥ → (∀ b, ∀ x ∈ N', e₂ (ρ₂ b x) ∈ N') →
      N' = N₂ := fun N' hle hne' hst => hmin false N' (fun t ht w hw => by
        simp only [Tp, if_false, Bool.false_eq_true] at ht
        obtain ⟨b, rfl⟩ := ht
        rw [hT₂]
        exact hst b w hw) hle hne'
  have hπ₁ := isIrreducible_mGenQuotRep he₁ hN₁e hN₁st hN₁0 hN₁min
  have hπ₂ := isIrreducible_mGenQuotRep he₂ hN₂e hN₂st hN₂0 hN₂min
  refine ⟨N₁, N₂, hN₁W, hN₂W, hN₁0, hN₂0, hN₁st, hN₂st, hπ₁, hπ₂, fun hschur => ?_⟩
  haveI := hπ₁
  haveI := hπ₂
  haveI := isIrreducible_outerTensor hπ₁ hπ₂ hschur

  obtain ⟨ψ₁, hψ₁⟩ : ∃ ψ : Dual ℂ W, ψ (n true) = 1 := by
    obtain ⟨f, hf⟩ : ∃ f : Dual ℂ W, f (n true) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hn0 true ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hcon)
    exact ⟨(f (n true))⁻¹ • f, by simp [hf]⟩
  obtain ⟨ψ₂, hψ₂⟩ : ∃ ψ : Dual ℂ W, ψ (n false) = 1 := by
    obtain ⟨f, hf⟩ : ∃ f : Dual ℂ W, f (n false) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hn0 false ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 hcon)
    exact ⟨(f (n false))⁻¹ • f, by simp [hf]⟩
  let E' : V →ₗ[ℂ] W := LinearMap.codRestrict W (e₁ * e₂) fun v => ⟨v, rfl⟩
  have hE' : ∀ w : W, E' w = w := fun w => Subtype.ext (hEw _ w.2)
  set l₁ : Dual ℂ V := ψ₁ ∘ₗ p true ∘ₗ E'
  set l₂ : Dual ℂ V := ψ₂ ∘ₗ p false ∘ₗ E'
  let n₁ : N₁ := ⟨(n true : V), ⟨n true, hnN true, rfl⟩⟩
  let n₂ : N₂ := ⟨(n false : V), ⟨n false, hnN false, rfl⟩⟩
  have hloc₁ : ∀ a, mGenQuotForm ρ₁ e₁ N₁ l₁ (mGenQuotRep ρ₁ e₁ N₁ a (mGenQuotMk ρ₁ e₁ N₁ n₁)) =
      c₁ a := by
    intro a
    rw [mGenQuotForm_apply]
    have : E' (e₁ (ρ₁ a n₁)) = T₁ a (n true) := by
      rw [← hT₁]
      exact hE' (T₁ a (n true))
    simp only [l₁, LinearMap.comp_apply]
    rw [this, hc₁, map_smul, hψ₁, smul_eq_mul, mul_one]
  have hloc₂ : ∀ b, mGenQuotForm ρ₂ e₂ N₂ l₂ (mGenQuotRep ρ₂ e₂ N₂ b (mGenQuotMk ρ₂ e₂ N₂ n₂)) =
      c₂ b := by
    intro b
    rw [mGenQuotForm_apply]
    have : E' (e₂ (ρ₂ b n₂)) = T₂ b (n false) := by
      rw [← hT₂]
      exact hE' (T₂ b (n false))
    simp only [l₂, LinearMap.comp_apply]
    rw [this, hc₂, map_smul, hψ₂, smul_eq_mul, mul_one]
  refine nonempty_equiv_of_matrixCoeff_eq' (v := (xs : V)) (l := φ ∘ₗ E')
    (w := mGenQuotMk ρ₁ e₁ N₁ n₁ ⊗ₜ mGenQuotMk ρ₂ e₂ N₂ n₂)
    (m := tensorForm (mGenQuotForm ρ₁ e₁ N₁ l₁) (mGenQuotForm ρ₂ e₂ N₂ l₂))
    (fun ⟨a, b⟩ => ?_) ⟨1, ?_⟩
  · rw [outerTensor_tmul, tensorForm_tmul, hloc₁, hloc₂, LinearMap.comp_apply]
    rw [← hcoefV a b]
    rfl
  · rw [LinearMap.comp_apply, map_one, Module.End.one_apply, hE', hφ1]
    exact one_ne_zero
end GroundTheory.Automorphic.RestrictedTensor
