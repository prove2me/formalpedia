-- Prove2me | solution 1 for LinearMap.exists_isBaseChange_extQuot_of_flat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/19dc341b-7f3a-539e-9b8d-e62286e0fc59

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v

namespace EP2Sol

open Function

section general

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

noncomputable abbrev φ (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (n : ℕ) :
    (Fin n → R) →ₗ[R] (Fin n → S) :=
  (Algebra.linearMap R S).compLeft (Fin n)

theorem φ_apply (n : ℕ) (v : Fin n → R) (i : Fin n) : φ R S n v i = algebraMap R S (v i) := rfl

theorem isBaseChange_φ (n : ℕ) : IsBaseChange S (φ R S n) :=
  IsBaseChange.finitePow (Fin n) (IsBaseChange.linearMap R S)

theorem mem_span_of_isBaseChange {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f) (y : N) :
    y ∈ Submodule.span S (Set.range f) := by
  induction y using hf.inductionOn with
  | zero => exact Submodule.zero_mem _
  | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
  | smul s n hn => exact Submodule.smul_mem _ s hn
  | add n₁ n₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂

theorem surjective_of_comp_eq {M N M' N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M'] [Module R M'] [Module S M'] [IsScalarTower R S M']
    [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']
    {α : M →ₗ[R] M'} {β : N →ₗ[R] N'} (hβ : IsBaseChange S β)
    (p : M →ₗ[R] N) (hp : Surjective p) (p' : M' →ₗ[S] N') (h : ∀ x, p' (α x) = β (p x)) :
    Surjective p' := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  intro y _
  have hy := mem_span_of_isBaseChange hβ y
  refine Submodule.span_le.mpr ?_ hy
  rintro _ ⟨n, rfl⟩
  obtain ⟨m, rfl⟩ := hp n
  exact ⟨α m, h m⟩

theorem bijective_of_isBaseChange_of_isBaseChange {M N₁ N₂ : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N₁] [Module R N₁] [Module S N₁] [IsScalarTower R S N₁]
    [AddCommGroup N₂] [Module R N₂] [Module S N₂] [IsScalarTower R S N₂]
    {f₁ : M →ₗ[R] N₁} {f₂ : M →ₗ[R] N₂} (h₁ : IsBaseChange S f₁) (h₂ : IsBaseChange S f₂)
    (c : N₁ →ₗ[S] N₂) (hc : ∀ m, c (f₁ m) = f₂ m) : Bijective c := by
  have e : c = (h₂.equiv.toLinearMap ∘ₗ h₁.equiv.symm.toLinearMap) := by
    apply h₁.algHom_ext
    intro m
    rw [hc, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.coe_toLinearMap, h₁.equiv_symm_apply,
      h₂.equiv_tmul, one_smul]
  rw [e]
  exact (h₁.equiv.symm.trans h₂.equiv).bijective

end general

section presentation

variable {B : Type u} [CommRing B] {B' : Type u} [CommRing B'] [Algebra B B'] [Module.Flat B B']
  {S : Type*} [AddCommGroup S] [Module B S] {S' : Type*} [AddCommGroup S'] [Module B S'] [Module B' S'] [IsScalarTower B B' S']
  {N : Type*} [AddCommGroup N] [Module B N] {N' : Type*} [AddCommGroup N'] [Module B N'] [Module B' N'] [IsScalarTower B B' N']
  {g : S →ₗ[B] S'} (hg : IsBaseChange B' g) {ν : N →ₗ[B] N'} (hν : IsBaseChange B' ν)

theorem linearMapLeftRightHom_comp {P : Type*} [AddCommGroup P] [Module B P] {P' : Type*} [AddCommGroup P'] [Module B P']
    [Module B' P'] [IsScalarTower B B' P'] {π : P →ₗ[B] S} {α : P →ₗ[B] P'} (hα : IsBaseChange B' α)
    (π' : P' →ₗ[B'] S') (hπ : ∀ x, π' (α x) = g (π x)) (δ : S →ₗ[B] N) :
    IsBaseChange.linearMapLeftRightHom hα ν (δ ∘ₗ π) = IsBaseChange.linearMapLeftRightHom hg ν δ ∘ₗ π' := by
  apply hα.algHom_ext
  intro x
  rw [IsBaseChange.linearMapLeftRightHom_comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, hπ,
    IsBaseChange.linearMapLeftRightHom_comp_apply]

theorem exact_lcomp {R : Type*} [CommRing R] {P Q T N : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup T] [Module R T] [AddCommGroup N] [Module R N]
    (a : Q →ₗ[R] P) (π : P →ₗ[R] T) (hex : Function.Exact a π) (hπ : Function.Surjective π) :
    Function.Exact (LinearMap.lcomp R N π) (LinearMap.lcomp R N a) ∧ Function.Injective (LinearMap.lcomp R N π) := by
  constructor
  · intro f
    constructor
    · intro hf

      have hker : LinearMap.ker π ≤ LinearMap.ker f := by
        intro x hx
        rw [LinearMap.mem_ker] at hx ⊢
        obtain ⟨y, rfl⟩ := (hex x).mp hx
        exact congrArg (fun φ => φ y) (show f ∘ₗ a = 0 from hf)
      refine ⟨(LinearMap.ker π).liftQ f hker ∘ₗ (LinearMap.quotKerEquivOfSurjective π hπ).symm.toLinearMap, ?_⟩
      apply LinearMap.ext
      intro y
      show ((LinearMap.ker π).liftQ f hker) ((LinearMap.quotKerEquivOfSurjective π hπ).symm (π y)) = f y
      have : (LinearMap.quotKerEquivOfSurjective π hπ).symm (π y) = Submodule.Quotient.mk y := by
        apply (LinearMap.quotKerEquivOfSurjective π hπ).injective
        rw [LinearEquiv.apply_symm_apply]
        rfl
      rw [this, Submodule.liftQ_apply]
    · rintro ⟨δ, rfl⟩
      apply LinearMap.ext
      intro x
      show δ (π (a x)) = 0
      rw [(hex (a x)).mpr ⟨x, rfl⟩, map_zero]
  · intro δ δ' h
    apply LinearMap.ext
    intro t
    obtain ⟨y, rfl⟩ := hπ t
    exact congrArg (fun φ => φ y) (show δ ∘ₗ π = δ' ∘ₗ π from h)

include hg hν in

theorem isBaseChange_linearMapLeftRightHom [Module.FinitePresentation B S] :
    IsBaseChange B' (IsBaseChange.linearMapLeftRightHom hg ν) := by
  classical

  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin B S
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  let π : (Fin n → B) →ₗ[B] S := e.symm.toLinearMap ∘ₗ K.mkQ
  let a : (Fin m → B) →ₗ[B] (Fin n → B) := Fintype.linearCombination B s
  have hπ : Function.Surjective π := e.symm.surjective.comp (Submodule.mkQ_surjective K)
  have hra : LinearMap.range a = K := by rw [Fintype.range_linearCombination]; exact hs
  have hex : Function.Exact a π := by
    rw [LinearMap.exact_iff, hra]
    ext x
    simp only [π, LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.map_eq_zero_iff,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

  have hφn : IsBaseChange B' (φ B B' n) := isBaseChange_φ n
  have hφm : IsBaseChange B' (φ B B' m) := isBaseChange_φ m
  let a' : (Fin m → B') →ₗ[B'] (Fin n → B') := hφm.lift (φ B B' n ∘ₗ a)
  let π' : (Fin n → B') →ₗ[B'] S' := hφn.lift (g ∘ₗ π)
  have ha' : ∀ x, a' (φ B B' m x) = φ B B' n (a x) := fun x => hφm.lift_eq _ x
  have hπ' : ∀ y, π' (φ B B' n y) = g (π y) := fun y => hφn.lift_eq _ y
  have hπ's : Function.Surjective π' := surjective_of_comp_eq hg π hπ π' hπ'

  have hcomp : π' ∘ₗ a' = 0 := by
    apply hφm.algHom_ext
    intro x
    rw [LinearMap.comp_apply, ha', hπ', (hex (a x)).mpr ⟨x, rfl⟩, map_zero, LinearMap.zero_apply]
  have hle : LinearMap.range a' ≤ LinearMap.ker π' := by
    rintro _ ⟨x, rfl⟩
    exact congrArg (fun ψ => ψ x) hcomp

  let C := (Fin n → B') ⧸ LinearMap.range a'
  have hKle : K ≤ LinearMap.ker ((LinearMap.range a').mkQ.restrictScalars B ∘ₗ φ B B' n) := by
    rw [← hra]
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply, ← ha', Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ⟨_, rfl⟩
  let h₃ : S →ₗ[B] C := K.liftQ ((LinearMap.range a').mkQ.restrictScalars B ∘ₗ φ B B' n) hKle ∘ₗ e.toLinearMap
  have hh₃ : ∀ y, h₃ (π y) = (LinearMap.range a').mkQ (φ B B' n y) := fun y => by
    show K.liftQ _ hKle (e (e.symm (K.mkQ y))) = _
    rw [LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]
    rfl
  have hbc₃ : IsBaseChange B' h₃ := by
    refine IsBaseChange.of_right_exact B' (φ B B' m) (φ B B' n) h₃ (f := a) (g := π) (f' := a')
      (g' := (LinearMap.range a').mkQ) ?_ ?_ hφm hφn hex hπ (LinearMap.exact_map_mkQ_range a') (Submodule.mkQ_surjective _)
    · exact LinearMap.ext fun x => (ha' x).symm
    · exact LinearMap.ext fun y => hh₃ y
  let c : C →ₗ[B'] S' := (LinearMap.range a').liftQ π' hle
  have hc : ∀ t, c (h₃ t) = g t := by
    intro t
    obtain ⟨y, rfl⟩ := hπ t
    rw [hh₃, Submodule.mkQ_apply, Submodule.liftQ_apply, hπ']
  have hcinj := (bijective_of_isBaseChange_of_isBaseChange hbc₃ hg c hc).1
  have hex' : Function.Exact a' π' := by
    intro y
    constructor
    · intro hy
      have : c (Submodule.Quotient.mk y) = c 0 := by rw [map_zero]; exact hy
      have := hcinj this
      exact (Submodule.Quotient.mk_eq_zero _).mp this
    · rintro ⟨x, rfl⟩
      exact congrArg (fun ψ => ψ x) hcomp

  obtain ⟨hexH, hinjH⟩ := exact_lcomp (N := N) a π hex hπ
  obtain ⟨hexH', hinjH'⟩ := exact_lcomp (N := N') a' π' hex' hπ's
  refine IsBaseChange.of_left_exact B' (IsBaseChange.linearMapLeftRightHom hg ν)
    (IsBaseChange.linearMapLeftRightHom hφn ν) (IsBaseChange.linearMapLeftRightHom hφm ν)
    (f := LinearMap.lcomp B N π) (g := LinearMap.lcomp B N a) (f' := LinearMap.lcomp B' N' π') (g' := LinearMap.lcomp B' N' a')
    ?_ ?_ (IsBaseChange.linearMapLeftRight hφn hν) (IsBaseChange.linearMapLeftRight hφm hν) hexH hinjH hexH' hinjH'
  · exact LinearMap.ext fun δ => linearMapLeftRightHom_comp hg hφn π' hπ' δ
  · exact LinearMap.ext fun f => linearMapLeftRightHom_comp hφn hφm a' ha' f

end presentation

end EP2Sol

open EP2Sol in
theorem solution
    {B : Type u} [CommRing B] [IsNoetherianRing B] {B' : Type u} [CommRing B'] [Algebra B B'] [Module.Flat B B']
    {M : Type v} [AddCommGroup M] [Module B M] {N : Type v} [AddCommGroup N] [Module B N]
    {M' : Type v} [AddCommGroup M'] [Module B M'] [Module B' M'] [IsScalarTower B B' M']
    {N' : Type v} [AddCommGroup N'] [Module B N'] [Module B' N'] [IsScalarTower B B' N']
    (μ : M →ₗ[B] M') (hμ : IsBaseChange B' μ) (ν : N →ₗ[B] N') (hν : IsBaseChange B' ν)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (hp : Function.Surjective p)
    (p' : (Fin r → B') →ₗ[B'] M') (hp' : ∀ v : Fin r → B, p' (fun i => algebraMap B B' (v i)) = μ (p v)) :
    Function.Surjective p' ∧
    ∃ (g : ↥(LinearMap.ker p) →ₗ[B] ↥(LinearMap.ker p'))
      (T : ((↥(LinearMap.ker p) →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N (LinearMap.ker p).subtype)) →ₗ[B]
           ((↥(LinearMap.ker p') →ₗ[B'] N') ⧸ LinearMap.range (LinearMap.lcomp B' N' (LinearMap.ker p').subtype))),
      (∀ (s : ↥(LinearMap.ker p)) (i : Fin r), ((g s : ↥(LinearMap.ker p')) : Fin r → B') i = algebraMap B B' ((s : Fin r → B) i)) ∧
      IsBaseChange B' T ∧
      (∀ δ : ↥(LinearMap.ker p) →ₗ[B] N, ∃ δ' : ↥(LinearMap.ker p') →ₗ[B'] N', ∀ s : ↥(LinearMap.ker p), δ' (g s) = ν (δ s)) ∧
      (∀ (δ : ↥(LinearMap.ker p) →ₗ[B] N) (δ' : ↥(LinearMap.ker p') →ₗ[B'] N'),
        (∀ s : ↥(LinearMap.ker p), δ' (g s) = ν (δ s)) →
        T (Submodule.Quotient.mk δ) = Submodule.Quotient.mk δ') := by
  classical
  have hφ : IsBaseChange B' (φ B B' r) := isBaseChange_φ r
  have hp'' : ∀ v, p' (φ B B' r v) = μ (p v) := hp'

  have hsurj : Function.Surjective p' := surjective_of_comp_eq hμ p hp p' hp''

  let g : ↥(LinearMap.ker p) →ₗ[B] ↥(LinearMap.ker p') :=
    LinearMap.codRestrict ((LinearMap.ker p').restrictScalars B) ((φ B B' r) ∘ₗ (LinearMap.ker p).subtype)
      (fun s => by
        show p' (φ B B' r s) = 0
        rw [hp'', (LinearMap.mem_ker).mp s.2, map_zero])
  have hgval : ∀ s : ↥(LinearMap.ker p), ((g s : ↥(LinearMap.ker p')) : Fin r → B') = φ B B' r s := fun s => rfl
  have hg : IsBaseChange B' g := by
    refine IsBaseChange.of_left_exact B' g (φ B B' r) μ (f := (LinearMap.ker p).subtype) (g := p)
      (f' := (LinearMap.ker p').subtype) (g' := p') ?_ ?_ hφ hμ ?_ ?_ ?_ ?_
    · exact LinearMap.ext fun s => rfl
    · exact LinearMap.ext fun v => (hp'' v).symm
    · exact LinearMap.exact_subtype_ker_map p
    · exact Subtype.val_injective
    · exact LinearMap.exact_subtype_ker_map p'
    · exact Subtype.val_injective

  haveI : Module.FinitePresentation B ↥(LinearMap.ker p) := by
    haveI : IsNoetherian B (Fin r → B) := isNoetherian_pi
    haveI : Module.Finite B ↥(LinearMap.ker p) := Module.Finite.of_fg (IsNoetherian.noetherian _)
    exact Module.finitePresentation_of_finite B _
  let θS := IsBaseChange.linearMapLeftRightHom hg ν
  let θF := IsBaseChange.linearMapLeftRightHom hφ ν
  have hθS : IsBaseChange B' θS := isBaseChange_linearMapLeftRightHom hg hν
  have hθF : IsBaseChange B' θF := IsBaseChange.linearMapLeftRight hφ hν

  let ρ : ((Fin r → B) →ₗ[B] N) →ₗ[B] (↥(LinearMap.ker p) →ₗ[B] N) := LinearMap.lcomp B N (LinearMap.ker p).subtype
  let ρ' : ((Fin r → B') →ₗ[B'] N') →ₗ[B'] (↥(LinearMap.ker p') →ₗ[B'] N') := LinearMap.lcomp B' N' (LinearMap.ker p').subtype
  have hcomm : ∀ f, θS (ρ f) = ρ' (θF f) := fun f =>
    linearMapLeftRightHom_comp hφ hg (LinearMap.ker p').subtype (fun s => rfl) f

  let E' := ((↥(LinearMap.ker p') →ₗ[B'] N') ⧸ LinearMap.range ρ')
  let T : ((↥(LinearMap.ker p) →ₗ[B] N) ⧸ LinearMap.range ρ) →ₗ[B] E' :=
    (LinearMap.range ρ).liftQ ((LinearMap.range ρ').mkQ.restrictScalars B ∘ₗ θS) (by
      rintro _ ⟨f, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hcomm, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      exact ⟨θF f, rfl⟩)
  have hT : IsBaseChange B' T := by
    refine IsBaseChange.of_right_exact B' θF θS T (f := ρ) (g := (LinearMap.range ρ).mkQ) (f' := ρ')
      (g' := (LinearMap.range ρ').mkQ) ?_ ?_ hθF hθS ?_ ?_ ?_ ?_
    · exact LinearMap.ext fun f => hcomm f
    · exact LinearMap.ext fun δ => rfl
    · exact LinearMap.exact_map_mkQ_range ρ
    · exact Submodule.mkQ_surjective _
    · exact LinearMap.exact_map_mkQ_range ρ'
    · exact Submodule.mkQ_surjective _
  refine ⟨hsurj, g, T, fun s i => rfl, hT, fun δ => ⟨θS δ, fun s => ?_⟩, fun δ δ' hδ => ?_⟩
  · exact IsBaseChange.linearMapLeftRightHom_comp_apply hg ν δ s
  · have hθ : θS δ = δ' := by
      apply hg.algHom_ext
      intro s
      rw [IsBaseChange.linearMapLeftRightHom_comp_apply, hδ]
    show Submodule.Quotient.mk (θS δ) = Submodule.Quotient.mk δ'
    rw [hθ]

end S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective
end P2MW
export P2MW.S_LinearMap_exists_isBaseChange_extQuot_of_flat_of_surjective (solution)
