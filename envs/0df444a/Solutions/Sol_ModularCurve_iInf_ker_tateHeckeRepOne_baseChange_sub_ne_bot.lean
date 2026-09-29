-- Prove2me | solution 1 for ModularCurve.iInf_ker_tateHeckeRepOne_baseChange_sub_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0415dc76-2d08-5c32-81be-59d6563acd1b

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_iInf_ker_tateHeckeRepOne_baseChange_sub_ne_bot

set_option autoImplicit false

namespace EigenNonzero

open Module

variable {K : Type*} [Field K]
variable {B : Type*} [CommRing B] [Algebra K B] (μ : B →ₐ[K] K)

def restrictAct {V : Type*} [AddCommGroup V] [Module K V] (ρ : B →ₐ[K] Module.End K V) (W : Submodule K V)
    (hW : ∀ (b : B) (v : V), v ∈ W → ρ b v ∈ W) : B →ₐ[K] Module.End K W where
  toFun b := (ρ b).restrict (fun v hv => hW b v hv)
  map_one' := by ext ⟨v, hv⟩; simp [LinearMap.restrict_apply]
  map_mul' a b := by ext ⟨v, hv⟩; simp [LinearMap.restrict_apply]
  map_zero' := by ext ⟨v, hv⟩; simp [LinearMap.restrict_apply]
  map_add' a b := by ext ⟨v, hv⟩; simp [LinearMap.restrict_apply]
  commutes' k := by
    ext ⟨v, hv⟩
    simp [LinearMap.restrict_apply, Algebra.algebraMap_eq_smul_one]

theorem restrictAct_apply {V : Type*} [AddCommGroup V] [Module K V] (ρ : B →ₐ[K] Module.End K V) (W : Submodule K V)
    (hW : ∀ (b : B) (v : V), v ∈ W → ρ b v ∈ W) (b : B) (w : W) :
    ((restrictAct ρ W hW b w : W) : V) = ρ b (w : V) := rfl

theorem exists_mul_sub_one_mem_ker {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : B →ₐ[K] Module.End K V) (b : B) (hb : Function.Bijective (ρ b)) : ∃ c : B, ρ (b * c - 1) = 0 := by

  let A : Subalgebra K (Module.End K V) := ρ.range
  haveI : FiniteDimensional K A := FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule A)
  let u : A := ⟨ρ b, ⟨b, rfl⟩⟩
  let L : A →ₗ[K] A := LinearMap.mulLeft K u
  have hLinj : Function.Injective L := by
    intro x y hxy
    apply Subtype.ext
    have h1 : (ρ b) * (x : Module.End K V) = (ρ b) * (y : Module.End K V) := congrArg Subtype.val hxy
    apply LinearMap.ext
    intro v
    have hv := LinearMap.congr_fun h1 v
    simp only [Module.End.mul_apply] at hv
    exact hb.1 hv
  have hLsurj : Function.Surjective L := LinearMap.injective_iff_surjective.mp hLinj
  obtain ⟨a, ha⟩ := hLsurj 1
  obtain ⟨c, hc⟩ := a.2
  refine ⟨c, ?_⟩
  rw [map_sub, map_one, map_mul, sub_eq_zero]
  have : ((L a : A) : Module.End K V) = 1 := congrArg Subtype.val ha
  rw [← this]
  show ρ b * ρ c = ρ b * (a : Module.End K V)
  rw [show ρ c = (a : Module.End K V) from hc]

theorem pow_apply_eq_zero_of_mem_ker_pow {V : Type*} [AddCommGroup V] [Module K V] (ρ : B →ₐ[K] Module.End K V)
    (a b : B) (ha : ∀ v, ρ b v = 0 → ρ a v = 0) (j : ℕ) (v : V) (hv : ((ρ b) ^ j) v = 0) : ρ (a ^ j) v = 0 := by
  induction j generalizing v with
  | zero =>
    simp only [pow_zero, Module.End.one_apply] at hv
    subst hv; simp
  | succ j ih =>

    have h1 : ((ρ b) ^ j) (ρ b v) = 0 := by
      rw [← Module.End.mul_apply, ← pow_succ, hv]
    have h2 : ρ (a ^ j) (ρ b v) = 0 := ih _ h1
    have h3 : ρ b (ρ (a ^ j) v) = 0 := by
      rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, h2]
    have h4 := ha _ h3
    rw [pow_succ, map_mul, Module.End.mul_apply]
    rwa [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply] at h4

universe u in

theorem exists_common_eigenvector (n : ℕ) :
    ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V], Module.finrank K V = n →
      ∀ ρ : B →ₐ[K] Module.End K V, (∀ a : B, ρ a = 0 → μ a = 0) →
        ∃ v : V, v ≠ 0 ∧ ∀ b : B, ρ b v = μ b • v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn ρ hann

  have hV : Nontrivial V := by
    by_contra htriv
    rw [not_nontrivial_iff_subsingleton] at htriv
    have : ρ 1 = 0 := by ext v; simp [Subsingleton.elim v 0]
    have := hann 1 this
    rw [map_one] at this
    exact one_ne_zero this
  by_cases h : ∃ b : B, μ b = 0 ∧ ρ b ≠ 0
  · obtain ⟨b₀, hμb₀, hρb₀⟩ := h
    set f : Module.End K V := ρ b₀ with hf

    have hfinj : ¬ Function.Injective f := by
      intro hinj
      have hbij : Function.Bijective f := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
      obtain ⟨c, hc⟩ := exists_mul_sub_one_mem_ker ρ b₀ hbij
      have := hann _ hc
      rw [map_sub, map_one, map_mul, hμb₀, zero_mul, zero_sub] at this
      exact one_ne_zero (neg_eq_zero.mp this)

    let V₁ : Submodule K V := LinearMap.ker f
    have hV₁inv : ∀ (b : B) (v : V), v ∈ V₁ → ρ b v ∈ V₁ := by
      intro b v hv
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hf, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
      show ρ b (f v) = 0
      rw [hv, map_zero]
    have hV₁lt : Module.finrank K V₁ < n := by
      rw [← hn]
      apply Submodule.finrank_lt
      intro htop
      apply hρb₀
      ext v
      have : v ∈ V₁ := htop ▸ Submodule.mem_top
      simpa [V₁] using this

    obtain ⟨m, hm, hm1⟩ := ((f.eventually_isCompl_ker_pow_range_pow).and (Filter.eventually_ge_atTop 1)).exists
    let W' : Submodule K V := LinearMap.range (f ^ m)
    have hW'inv : ∀ (b : B) (v : V), v ∈ W' → ρ b v ∈ W' := by
      rintro b v ⟨w, rfl⟩
      refine ⟨ρ b w, ?_⟩
      show (f ^ m) (ρ b w) = ρ b ((f ^ m) w)
      rw [hf, ← map_pow, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
    have hbijW' : Function.Bijective (restrictAct ρ W' hW'inv b₀) := by
      haveI : FiniteDimensional K W' := FiniteDimensional.finiteDimensional_submodule W'
      have hinj : Function.Injective (restrictAct ρ W' hW'inv b₀) := by
        intro x y hxy
        apply Subtype.ext
        have h1 : f (x : V) = f (y : V) := congrArg Subtype.val hxy
        have hsub : (x : V) - y ∈ LinearMap.ker f := by
          rw [LinearMap.mem_ker, map_sub, h1, sub_self]
        have hker : LinearMap.ker f ≤ LinearMap.ker (f ^ m) := by
          intro z hz
          rw [LinearMap.mem_ker] at hz ⊢
          obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le' hm1
          rw [pow_succ, Module.End.mul_apply, hz, map_zero]
        have hmemW : (x : V) - y ∈ LinearMap.ker (f ^ m) := hker hsub
        have hmemW' : (x : V) - y ∈ W' := W'.sub_mem x.2 y.2
        have := Submodule.disjoint_def.mp hm.disjoint _ hmemW hmemW'
        exact sub_eq_zero.mp this
      exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
    obtain ⟨c, hc⟩ := exists_mul_sub_one_mem_ker (restrictAct ρ W' hW'inv) b₀ hbijW'

    haveI : FiniteDimensional K V₁ := FiniteDimensional.finiteDimensional_submodule V₁
    obtain ⟨v₁, hv₁0, hv₁⟩ := ih _ hV₁lt V₁ rfl (restrictAct ρ V₁ hV₁inv) (by
      intro a ha

      have hker : ∀ v, f v = 0 → ρ a v = 0 := fun v hv => by
        have := LinearMap.congr_fun ha ⟨v, (LinearMap.mem_ker).mpr hv⟩
        exact congrArg Subtype.val this
      have hz : ρ (a ^ m * (b₀ * c - 1)) = 0 := by
        apply LinearMap.ext
        intro v
        obtain ⟨w, w', hw, hw', rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hm.codisjoint v
        rw [LinearMap.zero_apply, map_add]
        have e1 : ρ (a ^ m * (b₀ * c - 1)) w = 0 := by
          rw [mul_comm, map_mul, Module.End.mul_apply, pow_apply_eq_zero_of_mem_ker_pow ρ a b₀ hker m w hw, map_zero]
        have e2 : ρ (a ^ m * (b₀ * c - 1)) w' = 0 := by
          rw [map_mul, Module.End.mul_apply]
          have : ρ (b₀ * c - 1) w' = 0 := by
            have := LinearMap.congr_fun hc ⟨w', hw'⟩
            exact congrArg Subtype.val this
          rw [this, map_zero]
        rw [e1, e2, add_zero]
      have := hann _ hz
      rw [map_mul, map_sub, map_one, map_mul, hμb₀, zero_mul, zero_sub, mul_neg_one, neg_eq_zero, map_pow] at this
      exact pow_eq_zero_iff'.mp this |>.1)
    refine ⟨(v₁ : V), fun h0 => hv₁0 (Subtype.ext h0), fun b => ?_⟩
    have := hv₁ b
    exact congrArg Subtype.val this
  ·
    push Not at h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine ⟨v, hv, fun b => ?_⟩
    have hb : ρ (b - algebraMap K B (μ b)) = 0 := h _ (by simp)
    have := LinearMap.congr_fun hb v
    rw [map_sub, LinearMap.sub_apply, LinearMap.zero_apply, sub_eq_zero, AlgHom.commutes, Module.algebraMap_end_apply] at this
    exact this

section PadicField

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharZero K] [Algebra ℤ_[p] K]

theorem algebraMap_padicInt_injective : Function.Injective (algebraMap ℤ_[p] K) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 (PadicInt.irreducible_p (p := p))
  rw [map_mul, map_pow, mul_eq_zero] at hx
  rcases hx with h | h
  · exact (u.isUnit.map (algebraMap ℤ_[p] K)).ne_zero h
  · have : (algebraMap ℤ_[p] K) (p : ℤ_[p]) = (p : K) := map_natCast _ p
    rw [this] at h
    exact (NeZero.ne (p : K)) (pow_eq_zero_iff'.mp h).1

noncomputable def padicLift : ℚ_[p] →+* K :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (g := algebraMap ℤ_[p] K) fun y =>
    isUnit_iff_ne_zero.mpr fun h => nonZeroDivisors.ne_zero y.2
      ((injective_iff_map_eq_zero _).mp (algebraMap_padicInt_injective p K) _ h)

theorem padicLift_coe (c : ℤ_[p]) : padicLift p K (c : ℚ_[p]) = algebraMap ℤ_[p] K c :=
  IsLocalization.lift_eq _ c

end PadicField

section KeyLemma

open ModularCurve
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlgOne J]
variable [Module.Finite ℤ_[p] (TateModule p J)] [Module.Free ℤ_[p] (TateModule p J)]
variable (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K]
variable (Λ : ↥(rationalHeckeAlgebraOne p J) →+* K)
variable (hΛ : ∀ c : ℤ_[p], Λ (algebraMap ℚ_[p] ↥(rationalHeckeAlgebraOne p J) (c : ℚ_[p])) = algebraMap ℤ_[p] K c)

include hΛ in

theorem Λ_algebraMap (q : ℚ_[p]) : Λ (algebraMap ℚ_[p] ↥(rationalHeckeAlgebraOne p J) q) = padicLift p K q := by
  have : Λ.comp (algebraMap ℚ_[p] ↥(rationalHeckeAlgebraOne p J)) = padicLift p K := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    ext c
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [show algebraMap ℤ_[p] ℚ_[p] c = (c : ℚ_[p]) from rfl, hΛ, padicLift_coe]
  exact RingHom.congr_fun this q

include hΛ in
theorem Λ_smul (q : ℚ_[p]) (a : ↥(rationalHeckeAlgebraOne p J)) : Λ (q • a) = padicLift p K q * Λ a := by
  rw [Algebra.smul_def, map_mul, Λ_algebraMap p J K Λ hΛ]

include hΛ in
theorem sum_mul_Λ_eq_zero {α : Type} (s : Finset α) (k : α → K) (t : α → HeckeAlgOne)
    (h : ∑ a ∈ s, k a • (tateHeckeRepOne p J (t a)).baseChange K = 0) :
    ∑ a ∈ s, k a * Λ ⟨rationalHeckeRepOne p J (t a), rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J (t a)⟩ = 0 := by
  classical
  letI : Algebra ℚ_[p] K := (padicLift p K).toAlgebra
  have halg : ∀ q : ℚ_[p], algebraMap ℚ_[p] K q = padicLift p K q := fun q => rfl

  let bT := Module.Free.chooseBasis ℤ_[p] (TateModule p J)
  let ι := Module.Free.ChooseBasisIndex ℤ_[p] (TateModule p J)
  let bQ : Module.Basis ι ℚ_[p] (RationalTateModule p J) := Algebra.TensorProduct.basis ℚ_[p] bT
  let bK : Module.Basis ι K (K ⊗[ℤ_[p]] TateModule p J) := Algebra.TensorProduct.basis K bT
  let N : α → Matrix ι ι ℤ_[p] := fun a => LinearMap.toMatrix bT bT (tateHeckeRepOne p J (t a))

  have hK : ∑ a ∈ s, k a • (N a).map (algebraMap ℤ_[p] K) = 0 := by
    have := congrArg (LinearMap.toMatrix bK bK) h
    simp only [map_sum, map_smul, map_zero, bK, LinearMap.toMatrix_baseChange] at this
    exact this

  let φ : Module.End ℚ_[p] (RationalTateModule p J) ≃ₗ[ℚ_[p]] Matrix ι ι ℚ_[p] := LinearMap.toMatrix bQ bQ
  have hNQ : ∀ a, (N a).map (algebraMap ℤ_[p] ℚ_[p]) = φ (rationalHeckeRepOne p J (t a)) := by
    intro a
    rw [rationalHeckeRepOne_apply]
    exact (LinearMap.toMatrix_baseChange ℚ_[p] (tateHeckeRepOne p J (t a)) bT bT).symm
  let W : Submodule ℚ_[p] (Matrix ι ι ℚ_[p]) := (rationalHeckeAlgebraOne p J).toSubmodule.map φ.toLinearMap
  have hWmem : ∀ a, φ (rationalHeckeRepOne p J (t a)) ∈ W := fun a =>
    Submodule.mem_map_of_mem (rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J (t a))

  let w := Module.Basis.ofVectorSpace ℚ_[p] W
  let γs := Module.Basis.ofVectorSpaceIndex ℚ_[p] W
  haveI : Fintype γs := by
    haveI : FiniteDimensional ℚ_[p] (Matrix ι ι ℚ_[p]) := inferInstance
    exact FiniteDimensional.fintypeBasisIndex w

  let c : α → γs → ℚ_[p] := fun a γ => w.repr ⟨φ (rationalHeckeRepOne p J (t a)), hWmem a⟩ γ
  have hexpQ : ∀ a, φ (rationalHeckeRepOne p J (t a)) = ∑ γ, c a γ • ((w γ : W) : Matrix ι ι ℚ_[p]) := by
    intro a
    have := congrArg Subtype.val (w.sum_repr ⟨φ (rationalHeckeRepOne p J (t a)), hWmem a⟩).symm
    simpa only [Submodule.coe_sum, Submodule.coe_smul_of_tower] using this

  let f : ℚ_[p] →+* K := padicLift p K
  have hcomp : ∀ M : Matrix ι ι ℤ_[p], M.map (algebraMap ℤ_[p] K) = (M.map (algebraMap ℤ_[p] ℚ_[p])).map f := by
    intro M; ext i j
    simp only [Matrix.map_apply]
    exact (padicLift_coe p K (M i j)).symm
  have hsmulmap : ∀ (q : ℚ_[p]) (M : Matrix ι ι ℚ_[p]), (q • M).map f = f q • M.map f := by
    intro q M; ext i j; simp [Matrix.map_apply]
  have hsummap : ∀ (g : γs → Matrix ι ι ℚ_[p]), (∑ γ, g γ).map f = ∑ γ, (g γ).map f := by
    intro g; exact map_sum f.mapMatrix g Finset.univ
  let wK : γs → Matrix ι ι K := fun γ => ((w γ : W) : Matrix ι ι ℚ_[p]).map f
  have hexpK : ∀ a, (N a).map (algebraMap ℤ_[p] K) = ∑ γ, f (c a γ) • wK γ := by
    intro a
    rw [hcomp, hNQ, hexpQ, hsummap]
    exact Finset.sum_congr rfl fun γ _ => hsmulmap _ _

  have hwQ : LinearIndependent ℚ_[p] (fun γ : γs => ((w γ : W) : Matrix ι ι ℚ_[p])) :=
    w.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hwT : LinearIndependent K (fun γ : γs => (1 : K) ⊗ₜ[ℚ_[p]] ((w γ : W) : Matrix ι ι ℚ_[p])) :=
    Module.Flat.linearIndependent_one_tmul hwQ

  let eK : K ⊗[ℚ_[p]] Matrix ι ι ℚ_[p] →ₗ[K] Matrix ι ι K :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun kk => { toFun := fun M => kk • f.mapMatrix M, map_add' := fun M M' => by rw [map_add, smul_add],
                             map_smul' := fun q M => by
                               rw [RingHom.id_apply]
                               show kk • (q • M).map f = q • (kk • M.map f)
                               rw [hsmulmap, smul_comm]; rfl }
        map_add' := fun k1 k2 => by ext M; simp [add_smul]
        map_smul' := fun k1 k2 => by ext M; simp [mul_smul] }
  have heK : ∀ (kk : K) (M : Matrix ι ι ℚ_[p]), eK (kk ⊗ₜ M) = kk • M.map f := fun kk M => rfl
  have heKsymm : ∀ x, eK x = (matrixEquivTensor ι ℚ_[p] K).symm x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul kk M => rw [heK, matrixEquivTensor_apply_symm]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have heKinj : LinearMap.ker eK = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y hxy
    rw [heKsymm, heKsymm] at hxy
    exact (matrixEquivTensor ι ℚ_[p] K).symm.injective hxy
  have hwK : LinearIndependent K wK := by
    have := hwT.map' eK heKinj
    convert this using 1
    all_goals try rfl
    funext γ
    simp only [Function.comp_apply, heK, one_smul]
    rfl

  have hcoef : ∀ γ, ∑ a ∈ s, k a * f (c a γ) = 0 := by
    have hsum : ∑ γ, (∑ a ∈ s, k a * f (c a γ)) • wK γ = 0 := by
      rw [← hK]
      simp_rw [hexpK, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
    exact fun γ => (Fintype.linearIndependent_iff.mp hwK) _ hsum γ

  have hAmem : ∀ γ : γs, φ.symm ((w γ : W) : Matrix ι ι ℚ_[p]) ∈ rationalHeckeAlgebraOne p J := by
    intro γ
    obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.mp (w γ : W).2
    have : φ.symm ((w γ : W) : Matrix ι ι ℚ_[p]) = x := by
      rw [← hxe]; exact φ.symm_apply_apply x
    rw [this]; exact hx
  let aγ : γs → ↥(rationalHeckeAlgebraOne p J) := fun γ => ⟨φ.symm ((w γ : W) : Matrix ι ι ℚ_[p]), hAmem γ⟩
  have hrexp : ∀ a, (⟨rationalHeckeRepOne p J (t a), rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J (t a)⟩ :
      ↥(rationalHeckeAlgebraOne p J)) = ∑ γ, c a γ • aγ γ := by
    intro a
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    simp only [Subalgebra.coe_smul]
    apply φ.injective
    rw [hexpQ, map_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [map_smul]
    congr 1
    exact (φ.apply_symm_apply _).symm

  have hΛr : ∀ a, Λ ⟨rationalHeckeRepOne p J (t a), rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J (t a)⟩ =
      ∑ γ, f (c a γ) * Λ (aγ γ) := by
    intro a
    rw [hrexp]
    let Λa : ↥(rationalHeckeAlgebraOne p J) →+ K := Λ.toAddMonoidHom
    have hs := map_sum Λa (fun γ => c a γ • aγ γ) Finset.univ
    show Λa (∑ γ, c a γ • aγ γ) = _
    rw [hs]
    exact Finset.sum_congr rfl fun γ _ => show Λ _ = _ from Λ_smul p J K Λ hΛ _ _
  calc ∑ a ∈ s, k a * Λ ⟨rationalHeckeRepOne p J (t a), rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J (t a)⟩
      = ∑ a ∈ s, ∑ γ, k a * f (c a γ) * Λ (aγ γ) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hΛr, Finset.mul_sum]
        exact Finset.sum_congr rfl fun γ _ => (mul_assoc _ _ _).symm
    _ = ∑ γ, (∑ a ∈ s, k a * f (c a γ)) * Λ (aγ γ) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun γ _ => (Finset.sum_mul _ _ _).symm
    _ = 0 := by simp [hcoef]

end KeyLemma

section Assembly

open ModularCurve
open scoped TensorProduct

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlgOne J]
variable [Module.Finite ℤ_[p] (TateModule p J)] [Module.Free ℤ_[p] (TateModule p J)]
variable (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K]
variable (Λ : ↥(rationalHeckeAlgebraOne p J) →+* K)

noncomputable def hatHom : HeckeAlgOne →+* Module.End K (K ⊗[ℤ_[p]] TateModule p J) :=
  (Module.End.baseChangeHom ℤ_[p] K (TateModule p J)).toRingHom.comp (tateHeckeRepOne p J)

theorem hatHom_apply (t : HeckeAlgOne) : hatHom p J K t = (tateHeckeRepOne p J t).baseChange K := rfl

noncomputable def lamHom : HeckeAlgOne →+* K :=
  Λ.comp ((rationalHeckeRepOne p J).codRestrict (rationalHeckeAlgebraOne p J).toSubring.toSubsemiring
    (rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J))

theorem lamHom_apply (t : HeckeAlgOne) :
    lamHom p J K Λ t = Λ ⟨rationalHeckeRepOne p J t, rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J t⟩ := rfl

noncomputable abbrev Csub : Subalgebra K (Module.End K (K ⊗[ℤ_[p]] TateModule p J)) :=
  Algebra.adjoin K (Set.range (hatHom p J K))

theorem hatHom_comm : ∀ a ∈ Set.range (hatHom p J K), ∀ b ∈ Set.range (hatHom p J K), a * b = b * a := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

noncomputable scoped instance : CommSemiring ↥(Csub p J K) :=
  Algebra.adjoinCommSemiringOfComm (R := K) (hatHom_comm p J K)

noncomputable def rhoC : MvPolynomial (Nat.Primes ⊕ ℕ) K →ₐ[K] ↥(Csub p J K) :=
  MvPolynomial.aeval fun i => (⟨hatHom p J K (MvPolynomial.X i), Algebra.subset_adjoin (Set.mem_range_self _)⟩ : ↥(Csub p J K))

noncomputable def rhoB : MvPolynomial (Nat.Primes ⊕ ℕ) K →ₐ[K] Module.End K (K ⊗[ℤ_[p]] TateModule p J) :=
  (Csub p J K).val.comp (rhoC p J K)

noncomputable def muB : MvPolynomial (Nat.Primes ⊕ ℕ) K →ₐ[K] K :=
  MvPolynomial.aeval fun i => lamHom p J K Λ (MvPolynomial.X i)

theorem rhoB_map (t : HeckeAlgOne) : rhoB p J K (MvPolynomial.map (Int.castRingHom K) t) = hatHom p J K t := by
  have : (rhoB p J K).toRingHom.comp (MvPolynomial.map (Int.castRingHom K)) = hatHom p J K := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C, eq_intCast, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, map_intCast]
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [rhoB, AlgHom.comp_apply, rhoC, MvPolynomial.aeval_X]
      rfl
  exact RingHom.congr_fun this t

theorem muB_map (t : HeckeAlgOne) : muB p J K Λ (MvPolynomial.map (Int.castRingHom K) t) = lamHom p J K Λ t := by
  have : (muB p J K Λ).toRingHom.comp (MvPolynomial.map (Int.castRingHom K)) = lamHom p J K Λ := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_C, eq_intCast, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, map_intCast]
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [muB, MvPolynomial.aeval_X]
  exact RingHom.congr_fun this t

end Assembly

end EigenNonzero
p2m_reactivate "P2MW.S_ModularCurve_iInf_ker_tateHeckeRepOne_baseChange_sub_ne_bot.EigenNonzero"

open EigenNonzero ModularCurve in
open scoped TensorProduct in
theorem solution
    (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module ModularCurve.HeckeAlgOne J]
    [Module.Finite ℤ_[p] (TateModule p J)] [Module.Free ℤ_[p] (TateModule p J)]
    (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K]
    (Λ : ↥(ModularCurve.rationalHeckeAlgebraOne p J) →+* K)
    (hΛ : ∀ c : ℤ_[p],
      Λ (algebraMap ℚ_[p] ↥(ModularCurve.rationalHeckeAlgebraOne p J) (c : ℚ_[p])) = algebraMap ℤ_[p] K c) :
    (⨅ t : ModularCurve.HeckeAlgOne,
        LinearMap.ker ((ModularCurve.tateHeckeRepOne p J t).baseChange K - Λ ⟨ModularCurve.rationalHeckeRepOne p J t,
                  ModularCurve.rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J t⟩ • LinearMap.id)) ≠ ⊥ := by
  classical

  have hann : ∀ x : MvPolynomial (Nat.Primes ⊕ ℕ) K, rhoB p J K x = 0 → muB p J K Λ x = 0 := by
    intro x hx
    have hxsum : x = ∑ m ∈ x.support, MvPolynomial.coeff m x •
        MvPolynomial.map (Int.castRingHom K) (MvPolynomial.monomial m (1 : ℤ)) := by
      conv_lhs => rw [MvPolynomial.as_sum x]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.map_monomial, map_one, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have h1 : ∑ m ∈ x.support, MvPolynomial.coeff m x •
        (tateHeckeRepOne p J (MvPolynomial.monomial m (1 : ℤ))).baseChange K = 0 := by
      rw [hxsum, map_sum] at hx
      simpa only [map_smul, rhoB_map, hatHom_apply] using hx
    have h2 := sum_mul_Λ_eq_zero p J K Λ hΛ x.support (fun m => MvPolynomial.coeff m x)
      (fun m => MvPolynomial.monomial m (1 : ℤ)) h1
    rw [hxsum, map_sum]
    simp only [map_smul, muB_map, lamHom_apply, smul_eq_mul]
    exact h2
  obtain ⟨v, hv0, hv⟩ := exists_common_eigenvector (muB p J K Λ) (Module.finrank K (K ⊗[ℤ_[p]] TateModule p J))
    (K ⊗[ℤ_[p]] TateModule p J) rfl (rhoB p J K) hann
  intro hbot
  apply hv0
  have hmem : v ∈ (⨅ t : HeckeAlgOne,
      LinearMap.ker ((tateHeckeRepOne p J t).baseChange K -
        Λ ⟨rationalHeckeRepOne p J t, rationalHeckeRepOne_mem_rationalHeckeAlgebraOne p J t⟩ • LinearMap.id)) := by
    rw [Submodule.mem_iInf]
    intro t
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero,
      ← hatHom_apply, ← rhoB_map, hv, muB_map, lamHom_apply]
  rw [hbot] at hmem
  exact (Submodule.mem_bot K).mp hmem

end S_ModularCurve_iInf_ker_tateHeckeRepOne_baseChange_sub_ne_bot
end P2MW
export P2MW.S_ModularCurve_iInf_ker_tateHeckeRepOne_baseChange_sub_ne_bot (solution)
