-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_finite_etale_faithfullyFlat_finComb_basis_of_forall_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/0f6ae3c7-1f4f-54e9-adda-3aa2881ac145

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Theorems.Thm_Algebra_Etale_exists_isIdempotentElem_mul_eq_mul_and_not_mem_iff
import Theorems.Thm_Algebra_Etale_exists_finite_etale_forall_existsUnique_comp_eq
import Theorems.Thm_Algebra_Etale_finite_etale_faithfullyFlat_away_of_isIdempotentElem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_finite_etale_faithfullyFlat_finComb_basis_of_forall_isAlgClosed

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_finite_etale_faithfullyFlat_finComb_basis_of_forall_isAlgClosed.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "finComb IsCommutative pointGroup one_natural one mul_natural mk mul nsmul"
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

universe u

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

private noncomputable def _root_.GoodReductionJacobian.RelativeGroupLaw.compHom {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    letI := L.pointGroup t; letI := L.pointGroup t'
    SchemeHomOver t f →* SchemeHomOver t' f :=
  letI := L.pointGroup t; letI := L.pointGroup t'
  { toFun := schemeHomOverComp ψ hψ
    map_one' := L.one_natural t t' ψ hψ
    map_mul' := fun x y => L.mul_natural t t' ψ hψ x y }

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "compHom"
theorem nsmul_eq_pow {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (x : SchemeHomOver t f) :
    L.nsmul t n x = (letI := L.pointGroup t; x ^ n) := by
  letI := L.pointGroup t
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih =>
    rw [pow_succ, ← ih]
    rfl

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.finComb_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') {m : ℕ} (x : Fin m → SchemeHomOver t f) (c : Fin m → ℕ) :
    schemeHomOverComp ψ hψ (L.finComb t x c) = L.finComb t' (fun i => schemeHomOverComp ψ hψ (x i)) c := by
  letI := L.pointGroup t; letI := L.pointGroup t'
  show (L.compHom t t' ψ hψ) (L.finComb t x c) = L.finComb t' (fun i => (L.compHom t t' ψ hψ) (x i)) c
  unfold finComb
  rw [map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun i => by simp only [Function.comp_apply, map_pow]))

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "finComb_natural"

private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.nsmul_finComb_eq_one (hc : L.IsCommutative) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) {m : ℕ}
    (x : Fin m → SchemeHomOver t f) (hx : ∀ i, L.nsmul t n (x i) = L.one t) (c : Fin m → ℕ) :
    L.nsmul t n (L.finComb t x c) = L.one t := by
  letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := fun a b => hc t a b }
  have hx' : ∀ i, x i ^ n = 1 := fun i => by
    have := hx i; rw [nsmul_eq_pow] at this; exact this
  rw [nsmul_eq_pow]
  show (L.finComb t x c) ^ n = 1
  unfold finComb
  rw [← powMonoidHom_apply, map_list_prod, List.map_ofFn]
  · have : (⇑(powMonoidHom n) ∘ fun i => x i ^ c i) = fun _ => (1 : SchemeHomOver t f) := funext fun i => by
      simp only [Function.comp_apply, powMonoidHom_apply]
      rw [← pow_mul, mul_comm, pow_mul, hx' i, one_pow]
    rw [this, List.ofFn_const, List.prod_replicate, one_pow]

p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul_finComb_eq_one"
end GoodReductionJacobian.RelativeGroupLaw

noncomputable section

namespace B1dAux

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

def pt {B : Type} [CommRing B] [Algebra S B] (ι : Spec (CommRingCat.of B) ⟶ A)
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S B)))
    {C : Type} [CommRing C] [Algebra S C] (φ : B →ₐ[S] C) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S C))) f :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι, by
    rw [Category.assoc, hι, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun s => φ.commutes s⟩

@[scoped simp] theorem pt_val {B : Type} [CommRing B] [Algebra S B] (ι : Spec (CommRingCat.of B) ⟶ A)
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S B)))
    {C : Type} [CommRing C] [Algebra S C] (φ : B →ₐ[S] C) :
    (pt ι hι φ).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι := rfl

theorem nsmul_pt {B : Type} [CommRing B] [Algebra S B] (ι : Spec (CommRingCat.of B) ⟶ A)
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S B))) (n : ℕ)
    (hιn : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f),
      L.nsmul t n y = L.one t ↔ ∃ z : T ⟶ Spec (CommRingCat.of B), z ≫ ι = y.1)
    {C : Type} [CommRing C] [Algebra S C] (φ : B →ₐ[S] C) :
    L.nsmul _ n (pt ι hι φ) = L.one _ :=
  (hιn _ _ _).mpr ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), rfl⟩

theorem exists_algHom_of_nsmul {B : Type} [CommRing B] [Algebra S B] (ι : Spec (CommRingCat.of B) ⟶ A)
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S B))) (n : ℕ)
    (hιn : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f),
      L.nsmul t n y = L.one t ↔ ∃ z : T ⟶ Spec (CommRingCat.of B), z ≫ ι = y.1)
    {C : Type} [CommRing C] [Algebra S C] (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S C))) f)
    (hy : L.nsmul _ n y = L.one _) : ∃ φ : B →ₐ[S] C, y = pt ι hι φ := by
  obtain ⟨z, hz⟩ := (hιn _ _ y).mp hy
  obtain ⟨g, rfl⟩ := Spec.map_surjective z
  have hg : CommRingCat.ofHom (algebraMap S B) ≫ g = CommRingCat.ofHom (algebraMap S C) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← hι, ← Category.assoc, hz, y.2]
  refine ⟨{ toRingHom := g.hom, commutes' := fun r => ?_ }, ?_⟩
  · have := congrArg (fun k : CommRingCat.of S ⟶ CommRingCat.of C => k.hom r) hg
    simpa using this
  · apply Subtype.ext
    rw [pt_val, ← hz]
    rfl

theorem exhaust_of_injective
    {K : Scheme.{0}} (tk : K ⟶ Spec (CommRingCat.of S)) (n m : ℕ)
    (Pbar R : Fin m → SchemeHomOver tk f)
    (hPinj : ∀ c c' : Fin m → Fin n, L.finComb tk Pbar (fun i => (c i : ℕ)) = L.finComb tk Pbar (fun i => (c' i : ℕ)) → c = c')
    (hPex : ∀ Q : SchemeHomOver tk f, L.nsmul tk n Q = L.one tk → ∃ c : Fin m → Fin n, L.finComb tk Pbar (fun i => (c i : ℕ)) = Q)
    (hPtor : ∀ c : Fin m → Fin n, L.nsmul tk n (L.finComb tk Pbar (fun i => (c i : ℕ))) = L.one tk)
    (hRinj : ∀ c c' : Fin m → Fin n, L.finComb tk R (fun i => (c i : ℕ)) = L.finComb tk R (fun i => (c' i : ℕ)) → c = c')
    (hRtor : ∀ c : Fin m → Fin n, L.nsmul tk n (L.finComb tk R (fun i => (c i : ℕ))) = L.one tk) :
    ∀ Q : SchemeHomOver tk f, L.nsmul tk n Q = L.one tk → ∃ c : Fin m → Fin n, L.finComb tk R (fun i => (c i : ℕ)) = Q := by
  classical

  let Tor := {Q : SchemeHomOver tk f // L.nsmul tk n Q = L.one tk}

  let eP : (Fin m → Fin n) → Tor := fun c => ⟨L.finComb tk Pbar (fun i => (c i : ℕ)), hPtor c⟩
  have hePbij : Function.Bijective eP := by
    refine ⟨fun c c' h => hPinj c c' (congrArg Subtype.val h), fun Q => ?_⟩
    obtain ⟨c, hc⟩ := hPex Q.1 Q.2
    exact ⟨c, Subtype.ext hc⟩
  haveI : Finite Tor := Finite.of_surjective eP hePbij.2

  let eR : (Fin m → Fin n) → Tor := fun c => ⟨L.finComb tk R (fun i => (c i : ℕ)), hRtor c⟩
  have heRinj : Function.Injective eR := fun c c' h => hRinj c c' (congrArg Subtype.val h)
  have heRsurj : Function.Surjective eR := by

    let ePe : (Fin m → Fin n) ≃ Tor := Equiv.ofBijective eP hePbij
    have hinj' : Function.Injective (ePe.symm ∘ eR) := ePe.symm.injective.comp heRinj
    have hsurj' : Function.Surjective (ePe.symm ∘ eR) := Finite.surjective_of_injective hinj'
    intro Q
    obtain ⟨c, hc⟩ := hsurj' (ePe.symm Q)
    exact ⟨c, ePe.symm.injective hc⟩
  intro Q hQ
  obtain ⟨c, hc⟩ := heRsurj ⟨Q, hQ⟩
  exact ⟨c, congrArg Subtype.val hc⟩

theorem exists_prime_comap_eq_not_mem (hc : L.IsCommutative) (n m : ℕ)
    (B : Type) [CommRing B] [Algebra S B] [Module.Finite S B] [Algebra.Etale S B]
    (ι : Spec (CommRingCat.of B) ⟶ A) (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S B)))
    (hιc : IsClosedImmersion ι)
    (hιn : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f),
      L.nsmul t n y = L.one t ↔ ∃ z : T ⟶ Spec (CommRingCat.of B), z ≫ ι = y.1)
    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      ∃ P : Fin m → SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
        (∀ i, L.nsmul (Spec.map (CommRingCat.ofHom sk)) n (P i) = L.one (Spec.map (CommRingCat.ofHom sk))) ∧
        (∀ c c' : Fin m → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sk)) P (fun i => (c i : ℕ)) =
            L.finComb (Spec.map (CommRingCat.ofHom sk)) P (fun i => (c' i : ℕ)) → c = c') ∧
        (∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
          L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
          ∃ c : Fin m → Fin n, L.finComb (Spec.map (CommRingCat.ofHom sk)) P (fun i => (c i : ℕ)) = Q))
    (C : Type) [CommRing C] [Algebra S C] (u : Fin m → (B →ₐ[S] C))
    (huniv : ∀ (D : Type) [CommRing D] [Algebra S D] (v : Fin m → (B →ₐ[S] D)), ∃! w : C →ₐ[S] D, ∀ i, w.comp (u i) = v i)
    (φ : (Fin m → Fin n) → (B →ₐ[S] C))
    (hφ : ∀ c, L.finComb _ (fun i => pt ι hι (u i)) (fun i => (c i : ℕ)) = pt ι hι (φ c))
    (e : (Fin m → Fin n) → (Fin m → Fin n) → C)
    (he : ∀ (c c' : Fin m → Fin n) (𝔭 : Ideal C), 𝔭.IsPrime → (e c c' ∉ 𝔭 ↔ ∀ b : B, φ c b - φ c' b ∈ 𝔭))
    (𝔮 : Ideal S) (h𝔮 : 𝔮.IsPrime) :
    ∃ 𝔭 : Ideal C, 𝔭.IsPrime ∧ 𝔭.comap (algebraMap S C) = 𝔮 ∧ ∀ c c' : Fin m → Fin n, c ≠ c' → e c c' ∈ 𝔭 := by
  classical
  haveI := h𝔮

  let k : Type := AlgebraicClosure (FractionRing (S ⧸ 𝔮))
  let g : S ⧸ 𝔮 →+* k := (algebraMap (FractionRing (S ⧸ 𝔮)) k).comp (algebraMap (S ⧸ 𝔮) (FractionRing (S ⧸ 𝔮)))
  have hg : Function.Injective g :=
    (algebraMap (FractionRing (S ⧸ 𝔮)) k).injective.comp (IsFractionRing.injective (S ⧸ 𝔮) (FractionRing (S ⧸ 𝔮)))
  letI : Algebra S k := (g.comp (Ideal.Quotient.mk 𝔮)).toAlgebra
  have hker : RingHom.ker (algebraMap S k) = 𝔮 := by
    ext s
    rw [RingHom.mem_ker]
    show g (Ideal.Quotient.mk 𝔮 s) = 0 ↔ s ∈ 𝔮
    rw [map_eq_zero_iff g hg, Ideal.Quotient.eq_zero_iff_mem]

  obtain ⟨Pbar, hPtor, hPinj, -⟩ := hfib k (algebraMap S k)
  have hψ : ∀ i, ∃ ψ : B →ₐ[S] k, Pbar i = pt ι hι ψ := fun i =>
    exists_algHom_of_nsmul L ι hι n hιn (Pbar i) (hPtor i)
  choose ψ hψ using hψ
  obtain ⟨w, hw, -⟩ := huniv k ψ
  refine ⟨RingHom.ker w.toRingHom, RingHom.ker_isPrime _, ?_, ?_⟩
  · rw [RingHom.comap_ker, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap, hker]
  · intro c c' hcc'
    by_contra hmem
    have hagree : ∀ b : B, φ c b - φ c' b ∈ RingHom.ker w.toRingHom := (he c c' _ (RingHom.ker_isPrime _)).mp hmem
    have hwφ : w.comp (φ c) = w.comp (φ c') := by
      ext b
      have := hagree b
      rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, sub_eq_zero] at this
      exact this

    have hSw : Spec.map (CommRingCat.ofHom w.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)) =
        Spec.map (CommRingCat.ofHom (algebraMap S k)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
    have pt_comp : ∀ χ : B →ₐ[S] C,
        schemeHomOverComp (Spec.map (CommRingCat.ofHom w.toRingHom)) hSw (pt ι hι χ) = pt ι hι (w.comp χ) := by
      intro χ
      apply Subtype.ext
      rw [GoodReductionJacobian.schemeHomOverComp_coe, pt_val, pt_val, ← Category.assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      rfl
    have key : ∀ d : Fin m → Fin n,
        L.finComb _ Pbar (fun i => (d i : ℕ)) = pt ι hι (w.comp (φ d)) := by
      intro d
      have H := congrArg (schemeHomOverComp (Spec.map (CommRingCat.ofHom w.toRingHom)) hSw) (hφ d)
      rw [L.finComb_natural, pt_comp] at H
      rw [← H]
      congr 1
      funext i
      rw [pt_comp, hw i, hψ i]
    apply hcc'
    apply hPinj
    rw [key c, key c', hwφ]

end B1dAux
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_finite_etale_faithfullyFlat_finComb_basis_of_forall_isAlgClosed.B1dAux"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_finite_etale_faithfullyFlat_finComb_basis_of_forall_isAlgClosed.B1dAux"

open B1dAux in
theorem solution
    {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative) (n m : ℕ)

    (B : Type) [CommRing B] [Algebra S B] [Module.Finite S B] [Algebra.Etale S B]
    (ι : Spec (CommRingCat.of B) ⟶ A) (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S B)))
    (hιc : IsClosedImmersion ι)
    (hιn : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of S)) (y : SchemeHomOver t f),
      L.nsmul t n y = L.one t ↔ ∃ z : T ⟶ Spec (CommRingCat.of B), z ≫ ι = y.1)

    (hfib : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      ∃ P : Fin m → SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
        (∀ i, L.nsmul (Spec.map (CommRingCat.ofHom sk)) n (P i) = L.one (Spec.map (CommRingCat.ofHom sk))) ∧
        (∀ c c' : Fin m → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sk)) P (fun i => (c i : ℕ)) =
            L.finComb (Spec.map (CommRingCat.ofHom sk)) P (fun i => (c' i : ℕ)) → c = c') ∧
        (∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
          L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
          ∃ c : Fin m → Fin n, L.finComb (Spec.map (CommRingCat.ofHom sk)) P (fun i => (c i : ℕ)) = Q)) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra S S') (_ : Module.Finite S S') (_ : Algebra.Etale S S')
      (_ : Module.FaithfullyFlat S S')
      (P : Fin m → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) f),
      (∀ i, L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap S S'))) n (P i) =
        L.one (Spec.map (CommRingCat.ofHom (algebraMap S S')))) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k) (c c' : Fin m → Fin n),
        Spec.map (CommRingCat.ofHom sk) ≫
            (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c i : ℕ))).1 =
          Spec.map (CommRingCat.ofHom sk) ≫
            (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c' i : ℕ))).1 → c = c') ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k)
        (Q : SchemeHomOver (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) f),
        L.nsmul (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) n Q =
          L.one (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S S')))) →
        ∃ c : Fin m → Fin n,
          Spec.map (CommRingCat.ofHom sk) ≫
            (L.finComb (Spec.map (CommRingCat.ofHom (algebraMap S S'))) P (fun i => (c i : ℕ))).1 = Q.1) := by
  classical

  obtain ⟨C, _, _, _, _, u, huniv⟩ := Algebra.Etale.exists_finite_etale_forall_existsUnique_comp_eq S B m
  have hUtor : ∀ i, L.nsmul _ n (pt ι hι (u i)) = L.one _ := fun i => nsmul_pt L ι hι n hιn (u i)

  have hF : ∀ c : Fin m → Fin n, ∃ φ : B →ₐ[S] C, L.finComb _ (fun i => pt ι hι (u i)) (fun i => (c i : ℕ)) = pt ι hι φ :=
    fun c => exists_algHom_of_nsmul L ι hι n hιn _ (L.nsmul_finComb_eq_one hc _ n _ hUtor _)
  choose φ hφ using hF

  have hE : ∀ c c' : Fin m → Fin n, ∃ e : C, IsIdempotentElem e ∧
      (∀ 𝔭 : Ideal C, 𝔭.IsPrime → (e ∉ 𝔭 ↔ ∀ b : B, φ c b - φ c' b ∈ 𝔭)) ∧
      (∀ (k : Type) [Field k] (χ : C →+* k), χ.comp (φ c).toRingHom = χ.comp (φ c').toRingHom → χ e = 1) := by
    intro c c'
    obtain ⟨e, h1, -, -, h4, h5⟩ := Algebra.Etale.exists_isIdempotentElem_mul_eq_mul_and_not_mem_iff (φ c) (φ c')
    exact ⟨e, h1, h4, h5⟩
  choose e he1 he4 he5 using hE

  let pairs : Finset ((Fin m → Fin n) × (Fin m → Fin n)) := Finset.univ.filter (fun p => p.1 ≠ p.2)
  let d : C := ∏ p ∈ pairs, (1 - e p.1 p.2)
  have hd : IsIdempotentElem d :=
    Finset.prod_induction _ _ (fun a b ha hb => ha.mul hb) (IsIdempotentElem.one) (fun p _ => (he1 p.1 p.2).one_sub)
  have hsurj : ∀ 𝔮 : Ideal S, 𝔮.IsPrime → ∃ 𝔭 : Ideal C, 𝔭.IsPrime ∧ 𝔭.comap (algebraMap S C) = 𝔮 ∧ d ∉ 𝔭 := by
    intro 𝔮 h𝔮
    obtain ⟨𝔭, h𝔭, hcomap, hmem⟩ := exists_prime_comap_eq_not_mem L hc n m B ι hι hιc hιn hfib C u huniv φ hφ e he4 𝔮 h𝔮
    refine ⟨𝔭, h𝔭, hcomap, fun hdmem => ?_⟩
    haveI := h𝔭
    obtain ⟨p, hp, hp'⟩ := (Ideal.IsPrime.prod_mem_iff (p := 𝔭)).mp hdmem
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have := 𝔭.add_mem hp' (hmem p.1 p.2 hne)
    rw [sub_add_cancel] at this
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  obtain ⟨hfin, het, hff⟩ := Algebra.Etale.finite_etale_faithfullyFlat_away_of_isIdempotentElem d hd hsurj

  have hSS' : (algebraMap C (Localization.Away d)).comp (algebraMap S C) = algebraMap S (Localization.Away d) :=
    (IsScalarTower.algebraMap_eq S C (Localization.Away d)).symm
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away d))) ≫ Spec.map (CommRingCat.ofHom (algebraMap S C)) =
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away d))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hSS']
  let P : Fin m → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away d)))) f :=
    fun i => schemeHomOverComp _ hbase (pt ι hι (u i))

  have hPc : ∀ c : Fin m → Fin n,
      (L.finComb _ P (fun i => (c i : ℕ))).1 =
        Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away d))) ≫ Spec.map (CommRingCat.ofHom (φ c).toRingHom) ≫ ι := by
    intro c
    have := L.finComb_natural _ _ _ hbase (fun i => pt ι hι (u i)) (fun i => (c i : ℕ))
    rw [hφ c] at this
    rw [← this]
    rfl

  have inj : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : Localization.Away d →+* k) (c c' : Fin m → Fin n),
      Spec.map (CommRingCat.ofHom sk) ≫ (L.finComb _ P (fun i => (c i : ℕ))).1 =
        Spec.map (CommRingCat.ofHom sk) ≫ (L.finComb _ P (fun i => (c' i : ℕ))).1 → c = c' := by
    intro k _ _ sk c c' heq
    by_contra hne
    haveI : Mono ι := inferInstance
    let w : C →+* k := sk.comp (algebraMap C (Localization.Away d))
    have key : ∀ c₀ : Fin m → Fin n, Spec.map (CommRingCat.ofHom sk) ≫ (L.finComb _ P (fun i => (c₀ i : ℕ))).1 =
        Spec.map (CommRingCat.ofHom (w.comp (φ c₀).toRingHom)) ≫ ι := by
      intro c₀
      rw [hPc, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
    rw [key, key, cancel_mono] at heq
    have hw : w.comp (φ c).toRingHom = w.comp (φ c').toRingHom :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective heq)
    have h1 : w (e c c') = 1 := he5 c c' k w hw
    have hunit : IsUnit (w d) := ((IsLocalization.Away.algebraMap_isUnit d).map sk)
    apply hunit.ne_zero
    show w (∏ p ∈ pairs, (1 - e p.1 p.2)) = 0
    rw [map_prod]
    apply Finset.prod_eq_zero (i := (c, c')) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
    rw [map_sub, map_one, h1, sub_self]
  refine ⟨Localization.Away d, inferInstance, inferInstance, hfin, het, hff, P, ?_, inj, ?_⟩
  ·
    intro i
    exact (hιn _ _ _).mpr ⟨Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away d))) ≫
      Spec.map (CommRingCat.ofHom (u i).toRingHom), by simp only [Category.assoc]; rfl⟩
  ·
    intro k _ _ sk Q hQ
    have hR : Spec.map (CommRingCat.ofHom sk) ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away d))) =
        Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S (Localization.Away d)))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    let R : Fin m → SchemeHomOver (Spec.map (CommRingCat.ofHom (sk.comp (algebraMap S (Localization.Away d))))) f :=
      fun i => schemeHomOverComp _ hR (P i)
    have hRnat : ∀ c : Fin m → Fin n, schemeHomOverComp _ hR (L.finComb _ P (fun i => (c i : ℕ))) =
        L.finComb _ R (fun i => (c i : ℕ)) := fun c => L.finComb_natural _ _ _ hR P _
    obtain ⟨Pbar, hPtor, hPinj, hPex⟩ := hfib k (sk.comp (algebraMap S (Localization.Away d)))
    have hRtor : ∀ i, L.nsmul _ n (R i) = L.one _ := fun i =>
      (hιn _ _ _).mpr ⟨Spec.map (CommRingCat.ofHom sk) ≫ Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away d))) ≫
        Spec.map (CommRingCat.ofHom (u i).toRingHom), by simp only [Category.assoc]; rfl⟩
    have hRinj : ∀ c c' : Fin m → Fin n, L.finComb _ R (fun i => (c i : ℕ)) = L.finComb _ R (fun i => (c' i : ℕ)) → c = c' := by
      intro c c' h
      apply inj k sk c c'
      have := congrArg Subtype.val ((hRnat c).trans (h.trans (hRnat c').symm))
      exact this
    obtain ⟨c, hc'⟩ := exhaust_of_injective L _ n m Pbar R hPinj hPex
      (fun c => L.nsmul_finComb_eq_one hc _ n Pbar hPtor _) hRinj
      (fun c => L.nsmul_finComb_eq_one hc _ n R hRtor _) Q hQ
    refine ⟨c, ?_⟩
    rw [← hc', ← hRnat]
    rfl

end S_GoodReductionJacobian_RelativeGroupLaw_exists_finite_etale_faithfullyFlat_finComb_basis_of_forall_isAlgClosed
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_finite_etale_faithfullyFlat_finComb_basis_of_forall_isAlgClosed (solution)
