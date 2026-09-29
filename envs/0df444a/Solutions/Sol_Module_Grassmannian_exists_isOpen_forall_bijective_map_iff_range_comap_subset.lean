-- Prove2me | solution 1 for Module.Grassmannian.exists_isOpen_forall_bijective_map_iff_range_comap_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/acef780c-abfa-5df2-ae4c-bcb0a6af4c41

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Grassmannian_exists_isOpen_forall_bijective_map_iff_range_comap_subset

open scoped TensorProduct
open TensorProduct

set_option autoImplicit false

namespace GrassOpenS1b

lemma bijective_of_surjective_of_rankAtStalk (B P : Type) [CommRing B] [AddCommGroup P] [Module B P]
    [Module.Finite B P] [Module.Projective B P] (k : ℕ) (hk : ∀ p, Module.rankAtStalk (R := B) P p = k)
    (g : (Fin k → B) →ₗ[B] P) (hg : Function.Surjective g) : Function.Bijective g := by
  refine ⟨?_, hg⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
  obtain ⟨e, he₁, -⟩ := (LinearMap.exact_subtype_ker_map g).splitSurjectiveEquiv
    (Submodule.injective_subtype _) ⟨s, hs⟩

  let π : (Fin k → B) →ₗ[B] LinearMap.ker g := LinearMap.fst B _ P ∘ₗ e.toLinearMap
  have hπ : π ∘ₗ (LinearMap.ker g).subtype = LinearMap.id := by
    rw [he₁]
    ext x
    simp [π]
  haveI : Module.Projective B (LinearMap.ker g) := Module.Projective.of_split _ _ hπ
  haveI : Module.Finite B (LinearMap.ker g) :=
    Module.Finite.of_surjective π (fun x => ⟨x, LinearMap.congr_fun hπ x⟩)
  have hr : Module.rankAtStalk (R := B) (LinearMap.ker g) = 0 := by
    funext p
    haveI : Nontrivial B := by
      by_contra h
      haveI := not_nontrivial_iff_subsingleton.mp h
      exact IsEmpty.false p
    have h1 := congrFun (Module.rankAtStalk_eq_of_equiv e) p
    rw [Module.rankAtStalk_prod, Pi.add_apply, hk, Module.rankAtStalk_eq_finrank_of_free,
      Module.finrank_fin_fun] at h1
    change k = _ + k at h1
    simp only [Pi.zero_apply]
    omega
  have hbot : LinearMap.ker g = ⊥ := by
    have hsub := Module.rankAtStalk_eq_zero_iff_subsingleton.mp hr
    rw [eq_bot_iff]
    intro x hx
    have := Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker g) 0
    simpa using congrArg Subtype.val this
  exact LinearMap.ker_eq_bot.mp hbot

lemma subsingleton_tensor (R S T : Type) [CommRing R] [AddCommGroup S] [Module R S] [AddCommGroup T]
    [Module R T] [Subsingleton T] : Subsingleton (S ⊗[R] T) := by
  refine ⟨fun a b => ?_⟩
  have h : ∀ z : S ⊗[R] T, z = 0 := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim n 0, tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  rw [h a, h b]

variable (R : Type) [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M)
variable {A : Type} [CommRing A] [Algebra R A] (N : Module.Grassmannian A (A ⊗[R] M) k)

abbrev Q : Type := (A ⊗[R] M) ⧸ N.toSubmodule

def q0 (i : Fin k) : Q R N := N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)

def W : Submodule A (Q R N) := Submodule.span A (Set.range (q0 R x N))

abbrev K : Type := Q R N ⧸ W R x N

def U : Set (PrimeSpectrum A) :=
  (PrimeSpectrum.zeroLocus (Module.annihilator A (K R x N) : Set A))ᶜ

lemma isOpen_U : IsOpen (U R x N) := (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

lemma mem_U {p : PrimeSpectrum A} : p ∈ U R x N ↔ ¬ Module.annihilator A (K R x N) ≤ p.asIdeal := by
  simp [U, PrimeSpectrum.mem_zeroLocus]

section baseChange

variable (B : Type) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

omit [Algebra R B] [IsScalarTower R A B] in

lemma span_tmul_eq_top_iff :
    Submodule.span B (Set.range fun i => (1 : B) ⊗ₜ[A] q0 R x N i) = ⊤ ↔
      Subsingleton (B ⊗[A] K R x N) := by
  have hexact := lTensor_exact B (LinearMap.exact_subtype_mkQ (W R x N)) (Submodule.mkQ_surjective _)
  have hsurj := LinearMap.lTensor_surjective B (Submodule.mkQ_surjective (W R x N))
  have hrange : LinearMap.range (LinearMap.lTensor B (W R x N).subtype) =
      (Submodule.span B (Set.range fun i => (1 : B) ⊗ₜ[A] q0 R x N i)).restrictScalars A := by
    have h1 : LinearMap.range (LinearMap.lTensor B (W R x N).subtype) =
        ((W R x N).baseChange B).restrictScalars A := by
      ext z
      simp only [Submodule.baseChange, LinearMap.mem_range, Submodule.restrictScalars_mem]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨y, by rw [LinearMap.baseChange_eq_ltensor]⟩
      · rintro ⟨y, rfl⟩; exact ⟨y, by rw [LinearMap.baseChange_eq_ltensor]⟩
    rw [h1, W, Submodule.baseChange_span, ← Set.range_comp]
    rfl
  constructor
  · intro htop
    have hzero : ∀ z, LinearMap.lTensor B (W R x N).mkQ z = 0 := fun z => by
      have hz : z ∈ LinearMap.range (LinearMap.lTensor B (W R x N).subtype) := by
        rw [hrange, htop]; trivial
      exact (hexact z).mpr (LinearMap.mem_range.mp hz)
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := hsurj a
    obtain ⟨b, rfl⟩ := hsurj b
    rw [hzero, hzero]
  · intro hsub
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ LinearMap.range (LinearMap.lTensor B (W R x N).subtype) :=
      LinearMap.mem_range.mpr ((hexact z).mp (Subsingleton.elim _ _))
    rw [hrange] at hz
    exact hz

omit [Algebra R B] [IsScalarTower R A B] in

lemma subsingleton_iff_forall_mem_U :
    Subsingleton (B ⊗[A] K R x N) ↔
      ∀ q : PrimeSpectrum B, PrimeSpectrum.comap (algebraMap A B) q ∈ U R x N := by
  constructor
  · intro hs q
    rw [mem_U]
    intro hle
    set p := PrimeSpectrum.comap (algebraMap A B) q with hp_def
    have hp : p ∈ Module.support A (K R x N) := Module.mem_support_iff_of_finite.mpr hle
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
    let L := q.asIdeal.ResidueField
    have h1 : p.asIdeal ≤ RingHom.ker (Algebra.ofId A L) := fun a ha => by
      rw [RingHom.mem_ker]
      change algebraMap B L (algebraMap A B a) = 0
      rw [Ideal.algebraMap_residueField_eq_zero]
      exact ha
    have h2 : p.asIdeal.primeCompl ≤ (IsUnit.submonoid L).comap (Algebra.ofId A L) := fun a ha => by
      change IsUnit (algebraMap B L (algebraMap A B a))
      rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]
      exact ha
    let τ : p.asIdeal.ResidueField →ₐ[A] L := Ideal.ResidueField.liftₐ p.asIdeal (Algebra.ofId A L) h1 h2
    letI : Algebra p.asIdeal.ResidueField L := τ.toRingHom.toAlgebra
    haveI : IsScalarTower A p.asIdeal.ResidueField L :=
      IsScalarTower.of_algebraMap_eq fun a => (τ.commutes a).symm
    haveI : Nontrivial (L ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[A] K R x N)) :=
      inferInstance
    have e1 := AlgebraTensorModule.cancelBaseChange A p.asIdeal.ResidueField L L (K R x N)
    have e2 := AlgebraTensorModule.cancelBaseChange A B L L (K R x N)
    haveI : Subsingleton (L ⊗[B] (B ⊗[A] K R x N)) := subsingleton_tensor _ _ _
    haveI : Subsingleton (L ⊗[A] K R x N) := e2.symm.toEquiv.subsingleton
    haveI : Subsingleton (L ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[A] K R x N)) :=
      e1.toEquiv.subsingleton
    exact false_of_nontrivial_of_subsingleton
      (L ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[A] K R x N))
  · intro h
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    have hJ : Module.annihilator B (B ⊗[A] K R x N) ≠ ⊤ := by
      rw [Ne, Module.annihilator_eq_top_iff, ← not_nontrivial_iff_subsingleton]
      exact fun h' => h' hnt
    obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal _ hJ
    have := h ⟨m, hm.isPrime⟩
    rw [mem_U] at this
    apply this
    intro a ha
    change algebraMap A B a ∈ m
    apply hJm
    rw [Module.mem_annihilator]
    intro z
    rw [algebraMap_smul]
    induction z using TensorProduct.induction_on with
    | zero => rw [smul_zero]
    | tmul b y => rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, Module.mem_annihilator.mp ha y,
        tmul_zero]
    | add u v hu hv => rw [smul_add, hu, hv, add_zero]

lemma exists_equiv (f : A →ₐ[R] B) (hf : ∀ a, algebraMap A B a = f a) :
    ∃ e : ((B ⊗[R] M) ⧸ (Module.Grassmannian.map f N).toSubmodule) ≃ₗ[B] B ⊗[A] Q R N,
      ∀ i, e ((Module.Grassmannian.map f N).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i)) =
        (1 : B) ⊗ₜ[A] q0 R x N i := by
  have h : (Module.Grassmannian.map f N).toSubmodule =
      LinearMap.ker (Module.Grassmannian.baseChangeMkQ B N.toSubmodule) := by
    have h' : ‹Algebra A B› = f.toAlgebra := Algebra.algebra_ext _ _ fun a => by rw [hf]; rfl
    subst h'
    exact Module.Grassmannian.map_toSubmodule f N
  refine ⟨Submodule.quotEquivOfEq _ _ h ≪≫ₗ Module.Grassmannian.baseChangeMkQEquiv N.toSubmodule,
    fun i => ?_⟩
  rw [LinearEquiv.trans_apply, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
    Module.Grassmannian.baseChangeMkQEquiv,
    LinearMap.quotKerEquivOfSurjective_apply_mk, Module.Grassmannian.baseChangeMkQ,
    LinearMap.comp_apply, LinearEquiv.coe_coe, AlgebraTensorModule.cancelBaseChange_symm_tmul,
    LinearMap.baseChange_tmul]
  rfl

lemma bijective_iff (f : A →ₐ[R] B) (hf : ∀ a, algebraMap A B a = f a) :
    (Function.Bijective fun v : Fin k → B =>
        ∑ i, v i • (Module.Grassmannian.map f N).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i)) ↔
      Submodule.span B (Set.range fun i => (1 : B) ⊗ₜ[A] q0 R x N i) = ⊤ := by
  obtain ⟨e, he⟩ := exists_equiv R x N B f hf
  let N' := Module.Grassmannian.map f N
  let c : (Fin k → B) →ₗ[B] (B ⊗[R] M) ⧸ N'.toSubmodule :=
    Fintype.linearCombination B fun i => N'.toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i)
  have hc : ⇑c = fun v : Fin k → B => ∑ i, v i • N'.toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i) := rfl
  rw [← hc]
  have hr : (e : _ → _) '' Set.range (fun i => N'.toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i)) =
      Set.range (fun i => (1 : B) ⊗ₜ[A] q0 R x N i) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact he i
  have hspan : Function.Surjective c ↔
      Submodule.span B (Set.range fun i => (1 : B) ⊗ₜ[A] q0 R x N i) = ⊤ := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination,
      ← map_eq_top_iff (Submodule.orderIsoMapComap e), Submodule.orderIsoMapComap_apply,
      Submodule.map_span, ← hr]
    rfl
  constructor
  · exact fun hb => hspan.mp hb.2
  · intro htop
    exact bijective_of_surjective_of_rankAtStalk B _ k N'.rankAtStalk_eq c (hspan.mpr htop)

end baseChange

end GrassOpenS1b

open GrassOpenS1b in
theorem solution
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) (x : Fin k → M)
    (A : Type) [CommRing A] [Algebra R A] (N : Module.Grassmannian A (A ⊗[R] M) k) :
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ (B : Type) [CommRing B] [Algebra R B] (φ : A →ₐ[R] B),
        (Function.Bijective fun v : Fin k → B =>
            ∑ i, v i • (Module.Grassmannian.map φ N).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i)) ↔
          Set.range (PrimeSpectrum.comap φ.toRingHom) ⊆ U := by
  refine ⟨U R x N, isOpen_U R x N, fun B _ _ φ => ?_⟩
  letI : Algebra A B := φ.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  rw [Set.range_subset_iff, show φ.toRingHom = algebraMap A B from rfl,
    ← subsingleton_iff_forall_mem_U R x N B, ← span_tmul_eq_top_iff R x N B,
    bijective_iff R x N B φ (fun _ => rfl)]

end S_Module_Grassmannian_exists_isOpen_forall_bijective_map_iff_range_comap_subset
end P2MW
export P2MW.S_Module_Grassmannian_exists_isOpen_forall_bijective_map_iff_range_comap_subset (solution)
