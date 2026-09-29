-- Prove2me | solution 1 for MvPolynomial.exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/88563d79-180d-5fc8-91fb-670962768563

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential

set_option autoImplicit false

open KaehlerDifferential MvPolynomial

universe u

namespace SubmersiveQuotient

variable {R : Type u} [CommRing R] {ι : Type} [Finite ι] {m : ℕ} (h : Fin m → MvPolynomial (ι ⊕ Fin m) R)

abbrev V (ι : Type) (m : ℕ) : Type := (ι ⊕ Fin m) ⊕ Unit

abbrev Rel (m : ℕ) : Type := Fin m ⊕ Unit

noncomputable def Δ : MvPolynomial (ι ⊕ Fin m) R :=
  Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a))

noncomputable abbrev emb : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] MvPolynomial (V ι m) R := rename Sum.inl

noncomputable def rel : Rel m → MvPolynomial (V ι m) R :=
  fun r => Sum.elim (fun a => emb (h a)) (fun _ => emb (Δ h) * X (Sum.inr ()) - 1) r

@[scoped simp] theorem rel_inl (a : Fin m) : rel h (Sum.inl a) = emb (h a) := rfl
@[scoped simp] theorem rel_inr (x : Unit) : rel h (Sum.inr x) = emb (Δ h) * X (Sum.inr ()) - 1 := rfl

noncomputable def I : Ideal (MvPolynomial (V ι m) R) := Ideal.span (Set.range (rel h))

abbrev Q : Type u := MvPolynomial (V ι m) R ⧸ I h

noncomputable def φ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] Q h :=
  (Ideal.Quotient.mkₐ R (I h)).comp emb

theorem φ_apply (p : MvPolynomial (ι ⊕ Fin m) R) : φ h p = Ideal.Quotient.mk (I h) (emb p) := rfl

theorem rel_mem (r : Rel m) : rel h r ∈ I h := Ideal.subset_span ⟨r, rfl⟩

theorem φ_h (a : Fin m) : φ h (h a) = 0 := by
  rw [φ_apply, Ideal.Quotient.eq_zero_iff_mem]
  exact rel_mem h (Sum.inl a)

theorem φ_Δ_mul_Y : φ h (Δ h) * Ideal.Quotient.mk (I h) (X (Sum.inr ())) = 1 := by
  rw [φ_apply, ← map_mul, ← (Ideal.Quotient.mk (I h)).map_one, Ideal.Quotient.eq, ]
  exact rel_mem h (Sum.inr ())

theorem isUnit_φ_Δ : IsUnit (φ h (Δ h)) := isUnit_iff_exists_inv.mpr ⟨_, φ_Δ_mul_Y h⟩

theorem univ (B : Type u) [CommRing B] [Algebra R B] (ψ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] B)
    (hψ : ∀ a, ψ (h a) = 0) (hu : IsUnit (ψ (Δ h))) : ∃ χ : Q h →ₐ[R] B, χ.comp (φ h) = ψ := by
  obtain ⟨v, hv⟩ := hu
  let Ψ : MvPolynomial (V ι m) R →ₐ[R] B := aeval (Sum.elim (fun i => ψ (X i)) (fun _ => ((v⁻¹ : Bˣ) : B)))
  have hΨemb : ∀ p, Ψ (emb p) = ψ p := by
    intro p
    change aeval _ (rename Sum.inl p) = ψ p
    rw [aeval_rename]
    conv_rhs => rw [aeval_unique ψ]
    rfl
  have hΨI : ∀ x ∈ I h, Ψ x = 0 := by
    intro x hx
    unfold I at hx
    refine Submodule.span_induction ?_ (map_zero _) (fun x y _ _ hx hy => by rw [map_add, hx, hy, add_zero])
      (fun a x _ hx => by rw [smul_eq_mul, map_mul, hx, mul_zero]) hx
    rintro _ ⟨r, rfl⟩
    rcases r with a | u
    · rw [rel_inl, hΨemb, hψ]
    · rw [rel_inr, map_sub, map_mul, hΨemb, ← hv, map_one]
      change (v : B) * aeval _ (X (Sum.inr ())) - 1 = 0
      rw [aeval_X, Sum.elim_inr, Units.mul_inv, sub_self]
  refine ⟨Ideal.Quotient.liftₐ (I h) Ψ hΨI, ?_⟩
  ext p
  · change Ideal.Quotient.liftₐ (I h) Ψ hΨI (Ideal.Quotient.mk (I h) (emb (X p))) = ψ (X p)
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    exact hΨemb (X p)

noncomputable def gens : Algebra.Generators R (Q h) (V ι m) where
  val v := Ideal.Quotient.mk (I h) (X v)
  σ' c := (Ideal.Quotient.mk_surjective c).choose
  aeval_val_σ' c := by
    have hev : (aeval fun v => Ideal.Quotient.mk (I h) (X v) : MvPolynomial (V ι m) R →ₐ[R] Q h) =
        Ideal.Quotient.mkₐ R (I h) := by
      rw [aeval_unique (Ideal.Quotient.mkₐ R (I h))]
      rfl
    rw [hev]
    exact (Ideal.Quotient.mk_surjective c).choose_spec
  algebra := inferInstance
  algebraMap_eq := by
    have hev : (aeval fun v => Ideal.Quotient.mk (I h) (X v) : MvPolynomial (V ι m) R →ₐ[R] Q h) =
        Ideal.Quotient.mkₐ R (I h) := by
      rw [aeval_unique (Ideal.Quotient.mkₐ R (I h))]
      rfl
    rw [hev]
    rfl

theorem gens_val (v : V ι m) : (gens h).val v = Ideal.Quotient.mk (I h) (X v) := rfl

theorem gens_ker : (gens h).ker = I h := by
  change RingHom.ker (algebraMap (MvPolynomial (V ι m) R) (Q h)) = I h
  exact Ideal.mk_ker

noncomputable def pres : Algebra.PreSubmersivePresentation R (Q h) (V ι m) (Rel m) where
  toGenerators := gens h
  relation := rel h
  span_range_relation_eq_ker := by rw [gens_ker]; rfl
  map := Sum.map Sum.inr id
  map_inj := Sum.map_injective.mpr ⟨Sum.inr_injective, fun _ _ h => h⟩

theorem pderiv_inr_emb (p : MvPolynomial (ι ⊕ Fin m) R) : pderiv (Sum.inr ()) (emb p : MvPolynomial (V ι m) R) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [show (emb (MvPolynomial.C a) : MvPolynomial (V ι m) R) = MvPolynomial.C a from rename_C _ _, pderiv_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | mul_X p i hp =>
    rw [map_mul, Derivation.leibniz, hp, smul_zero, add_zero, show (emb (X i) : MvPolynomial (V ι m) R) = X (Sum.inl i) from rename_X _ _,
      pderiv_X_of_ne (by simp), smul_zero]

theorem pderiv_inl_emb (j : ι ⊕ Fin m) (p : MvPolynomial (ι ⊕ Fin m) R) :
    pderiv (Sum.inl j) (emb p : MvPolynomial (V ι m) R) = emb (pderiv j p) :=
  pderiv_rename Sum.inl_injective j p

theorem jacobiMatrix_eq :
    (pres h).jacobiMatrix =
      Matrix.fromBlocks
        ((Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)).transpose.map (emb : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] MvPolynomial (V ι m) R))
        (Matrix.of fun (a : Fin m) (_ : Unit) => pderiv (Sum.inl (Sum.inr a)) (emb (Δ h) * X (Sum.inr ()) - 1))
        0
        (Matrix.of fun (_ _ : Unit) => (emb (Δ h) : MvPolynomial (V ι m) R)) := by
  refine Matrix.ext fun i j => ?_
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rcases i with a | x <;> rcases j with b | y
  ·
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply]
    change pderiv (Sum.inl (Sum.inr a)) (emb (h b)) = emb (pderiv (Sum.inr a) (h b))
    exact pderiv_inl_emb _ _
  ·
    simp only [Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    rfl
  ·
    simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    change pderiv (Sum.inr x) (emb (h b)) = 0
    cases x
    exact pderiv_inr_emb _
  ·
    simp only [Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
    change pderiv (Sum.inr x) (emb (Δ h) * X (Sum.inr ()) - 1) = emb (Δ h)
    cases x
    rw [map_sub, Derivation.map_one_eq_zero, sub_zero, Derivation.leibniz, pderiv_X_self, pderiv_inr_emb, smul_zero,
      add_zero, smul_eq_mul, mul_one]

theorem jacobian_eq : (pres h).jacobian = φ h (Δ h) * φ h (Δ h) := by
  classical
  have hD : (Matrix.of fun (_ _ : Unit) => (emb (Δ h) : MvPolynomial (V ι m) R)).det = emb (Δ h) :=
    Matrix.det_unique _
  have hA : ((Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)).transpose.map
      (emb : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] MvPolynomial (V ι m) R)).det = emb (Δ h) := by
    change (AlgHom.mapMatrix (emb : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] MvPolynomial (V ι m) R)
      (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)).transpose).det = _
    rw [← AlgHom.map_det, Matrix.det_transpose]
    rfl
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, jacobiMatrix_eq, Matrix.det_fromBlocks_zero₂₁,
    hA, hD, map_mul]
  rfl

noncomputable def spres : Algebra.SubmersivePresentation R (Q h) (V ι m) (Rel m) where
  toPreSubmersivePresentation := pres h
  jacobian_isUnit := by rw [jacobian_eq]; exact (isUnit_φ_Δ h).mul (isUnit_φ_Δ h)

private theorem _root_.SubmersiveQuotient.isStandardSmooth : Algebra.IsStandardSmooth R (Q h) := (spres h).isStandardSmooth

p2m_export "SubmersiveQuotient" "isStandardSmooth"
theorem isCompl_range :
    IsCompl (Set.range (fun i : ι => (Sum.inl (Sum.inl i) : V ι m))) (Set.range (pres h).map) := by
  constructor
  · rw [Set.disjoint_iff]
    rintro v ⟨⟨i, rfl⟩, ⟨r, hr⟩⟩
    rcases r with a | x
    · simp [pres] at hr
    · simp [pres] at hr
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    change v ∈ (Set.range fun i : ι => (Sum.inl (Sum.inl i) : V ι m)) ∪ Set.range (pres h).map
    rcases v with (i | a) | x
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨Sum.inl a, rfl⟩
    · exact Or.inr ⟨Sum.inr x, rfl⟩

noncomputable def basis : Module.Basis ι (Q h) Ω[Q h⁄R] :=
  (spres h).basisKaehlerOfIsCompl (f := fun i : ι => (Sum.inl (Sum.inl i) : V ι m))
    (fun _ _ hij => by simpa using hij) (isCompl_range h)

theorem basis_apply (i : ι) : basis h i = D R (Q h) (φ h (X (Sum.inl i))) := by
  rw [basis, Algebra.SubmersivePresentation.basisKaehlerOfIsCompl_apply]
  change D R (Q h) (Ideal.Quotient.mk (I h) (X (Sum.inl (Sum.inl i)))) = D R (Q h) (Ideal.Quotient.mk (I h) (emb (X (Sum.inl i))))
  rw [show (emb (X (Sum.inl i)) : MvPolynomial (V ι m) R) = X (Sum.inl (Sum.inl i)) from rename_X _ _]

theorem main :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (φ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] C),
      Algebra.IsStandardSmooth R C ∧
      (∀ a, φ (h a) = 0) ∧
      IsUnit (φ (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)))) ∧
      (∀ (B : Type u) [CommRing B] [Algebra R B] (ψ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] B),
          (∀ a, ψ (h a) = 0) →
          IsUnit (ψ (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)))) →
          ∃ χ : C →ₐ[R] B, χ.comp φ = ψ) ∧
      ∃ b : Module.Basis ι C Ω[C⁄R], ∀ i, b i = D R C (φ (MvPolynomial.X (Sum.inl i))) :=
  ⟨Q h, inferInstance, inferInstance, φ h, isStandardSmooth h, φ_h h, isUnit_φ_Δ h,
    fun B _ _ ψ hψ hu => univ h B ψ hψ hu, basis h, basis_apply h⟩

end SubmersiveQuotient
p2m_reactivate "P2MW.S_MvPolynomial_exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential.SubmersiveQuotient"

theorem solution
    {R : Type u} [CommRing R] {ι : Type} [Finite ι] {m : ℕ} (h : Fin m → MvPolynomial (ι ⊕ Fin m) R) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (φ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] C),
      Algebra.IsStandardSmooth R C ∧
      (∀ a, φ (h a) = 0) ∧
      IsUnit (φ (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)))) ∧
      (∀ (B : Type u) [CommRing B] [Algebra R B] (ψ : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] B),
          (∀ a, ψ (h a) = 0) →
          IsUnit (ψ (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a)))) →
          ∃ χ : C →ₐ[R] B, χ.comp φ = ψ) ∧
      ∃ b : Module.Basis ι C Ω[C⁄R], ∀ i, b i = D R C (φ (MvPolynomial.X (Sum.inl i))) :=
  SubmersiveQuotient.main h

end S_MvPolynomial_exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential
end P2MW
export P2MW.S_MvPolynomial_exists_isStandardSmooth_algHom_isUnit_det_pderiv_basis_kaehlerDifferential (solution)
