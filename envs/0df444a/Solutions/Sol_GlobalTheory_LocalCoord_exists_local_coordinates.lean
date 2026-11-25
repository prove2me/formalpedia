-- Prove2me | solution 1 for GlobalTheory.LocalCoord.exists_local_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:28.709797+00:00
-- url     : https://prove2.me/submissions/72e5e3cd-50f6-4ad4-9418-4b1858c37474

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLocalCoordinates
import Theorems.Thm_GlobalTheory_LocalCoord_exists_frobenius
import Theorems.Thm_GlobalTheory_LocalCoord_span_of_derivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.LocalCoord
namespace GlobalTheory.LocalCoord
theorem _root_.solution :
    ∀ (k A K B : Type) [Field k] [Finite k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra k K] [CommRing B] [Algebra K B] (φ : TensorProduct k K A →ₐ[K] B) (χ : B →ₐ[K] K) (g : ℕ) (m : Ideal A), Function.Surjective φ → RingHom.ker φ ≤ nilradical _ → (∀ a : A, a ∈ m ↔ χ (φ (1 ⊗ₜ a)) = 0) → m.IsMaximal → (∃ (t : Fin g → B) (s : B), χ s ≠ 0 ∧ (∀ i, χ (t i) = 0) ∧ ∀ b, χ b = 0 → s * b ∈ Ideal.span (Set.range t)) → IsReduced B → ∃ (u : Fin g → A) (s : A), s ∉ m ∧ (∀ i, u i ∈ m) ∧ ∀ a ∈ m, s * a ∈ Ideal.span (Set.range u) ⊔ nilradical A := by
  intro k A K B _ _ _ _ _ _ _ _ _ φ χ g m hφ hker hm hmax ⟨t, s, hs, ht, hb⟩ _
  classical
  letI := Ideal.Quotient.field m
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨F, hF, hF2⟩ := exists_frobenius k A m hmax
  let ι : A →ₐ[k] K := ((χ.comp φ).restrictScalars k).comp Algebra.TensorProduct.includeRight
  have hι : ∀ a, ι a = χ (φ (1 ⊗ₜ a)) := fun a => rfl
  let ι' : (A ⧸ m) →+* K := Ideal.Quotient.lift m ι fun a ha => (hm a).mp ha
  let N' : Submodule (A ⧸ m) m.Cotangent :=
    Submodule.span _ {y | ∃ x : m, (x : A) ∈ nilradical A ∧ m.toCotangent x = y}
  haveI : Module.Finite A m.Cotangent :=
    Module.Finite.of_surjective m.toCotangent m.toCotangent_surjective
  haveI : Module.Finite (A ⧸ m) m.Cotangent := Module.Finite.of_restrictScalars_finite A _ _
  let r := Module.finrank (A ⧸ m) (m.Cotangent ⧸ N')
  let b := Module.finBasis (A ⧸ m) (m.Cotangent ⧸ N')
  let p : m → m.Cotangent ⧸ N' := fun x => N'.mkQ (m.toCotangent x)
  have hpadd : ∀ x y, p (x + y) = p x + p y := fun x y => by simp only [p, map_add]
  have hpsmul : ∀ (a : A) x, p (a • x) = Ideal.Quotient.mk m a • p x := fun a x => by
    simp only [p, map_smul]; rfl
  have hpsurj : Function.Surjective p := N'.mkQ_surjective.comp m.toCotangent_surjective
  let L : m → Fin r → K := fun x j => ι' (b.repr (p x) j)
  have hLadd : ∀ x y, L (x + y) = L x + L y := fun x y => by
    ext j; simp only [L, hpadd, map_add, Finsupp.add_apply, Pi.add_apply]
  have hLsmul : ∀ (a : A) x, L (a • x) = ι a • L x := fun a x => by
    ext j
    simp only [L, hpsmul, map_smul, Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    rfl
  let D : A →ₗ[k] Fin r → K :=
    { toFun := fun a => L ⟨a - F a, hF a⟩
      map_add' := fun a a' => by
        rw [← hLadd]; congr 1; ext; simp only [map_add, Submodule.coe_add]; ring
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← algebraMap_smul K c (L _), ← ι.commutes, ← hLsmul]
        congr 1; ext
        change c • a - F (c • a) = algebraMap k A c * (a - F a)
        rw [map_smul, ← Algebra.smul_def, smul_sub] }
  have hιF : ∀ a, ι (F a) = ι a := fun a => by
    have := (hm _).mp (hF a)
    rw [← hι, map_sub, sub_eq_zero] at this
    exact this.symm
  obtain ⟨w, hw⟩ := span_of_derivation φ χ hφ hker t s hs ht hb D (fun a a' => by
      change L _ = ι a • L _ + ι a' • L _
      rw [← hιF a', ← hLsmul, ← hLsmul, ← hLadd]
      congr 1; ext
      simp only [map_mul, Submodule.coe_add, SetLike.val_smul, smul_eq_mul]
      ring) (fun a ha => by
      have : p ⟨a - F a, hF a⟩ = 0 := by
        refine (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨_, ?_, rfl⟩)
        exact sub_mem ha ((mem_nilradical.mp ha).map F)
      change L _ = 0
      ext j
      simp [L, this])
  choose v hv using hpsurj
  have hDL : ∀ x : m, D x = L x := fun x => by
    obtain ⟨c, hc⟩ := hF2 x
    have h1 : L x = L ⟨x - F x, hF x⟩ + L ((x * c : A) • x) := by
      rw [← hLadd]; congr 1; ext
      simp only [hc, Submodule.coe_add, SetLike.val_smul, smul_eq_mul]
      ring
    rw [h1, hLsmul, map_mul, hι, (hm _).mp x.2, zero_mul, zero_smul, add_zero]
    rfl
  have hrg : r ≤ g := by
    have htop : Submodule.span K (Set.range w) = ⊤ := by
      rw [eq_top_iff, ← (Pi.basisFun K (Fin r)).span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have : Pi.basisFun K (Fin r) j = D (v (b j)) := by
        rw [hDL]
        ext i
        simp only [L, hv, Module.Basis.repr_self, Pi.basisFun_apply, Finsupp.single_apply,
          Pi.single_apply]
        by_cases h : j = i
        · simp [h]
        · simp [h, Ne.symm h]
      rw [this]
      exact hw _ ((hm _).mp (v (b j)).2)
    have := finrank_range_le_card (R := K) w
    rwa [Set.finrank, htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at this
  let u : Fin g → A := fun i => if h : i.1 < r then (v (b ⟨i.1, h⟩) : A) else 0
  have hu : ∀ j : Fin r, (v (b j) : A) ∈ Ideal.span (Set.range u) := fun j =>
    Ideal.subset_span ⟨⟨j.1, lt_of_lt_of_le j.2 hrg⟩, by simp [u]⟩
  have hle : m ≤ (Ideal.span (Set.range u) ⊔ nilradical A) ⊔ m • m := by
    set J := (Ideal.span (Set.range u) ⊔ nilradical A) ⊔ m • m with hJ
    have hk : ∀ y ∈ N', ∀ x : m, m.toCotangent x = y → (x : A) ∈ J := by
      intro y hy
      have : ∃ z : m, (z : A) ∈ nilradical A ∧ m.toCotangent z = y := by
        induction hy using Submodule.span_induction with
        | mem y h => exact h
        | zero => exact ⟨0, zero_mem _, map_zero _⟩
        | add y y' _ _ h h' =>
          obtain ⟨z, hz, rfl⟩ := h
          obtain ⟨z', hz', rfl⟩ := h'
          exact ⟨z + z', add_mem hz hz', map_add _ _ _⟩
        | smul c y _ h =>
          obtain ⟨z, hz, rfl⟩ := h
          obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
          exact ⟨c • z, Ideal.mul_mem_left _ _ hz, by rw [map_smul]; rfl⟩
      obtain ⟨z, hz, rfl⟩ := this
      intro x hx
      have h2 := m.toCotangent_eq.mp hx
      have : (x : A) = z + (x - z) := by ring
      rw [this]
      refine add_mem (Ideal.mem_sup_left (Ideal.mem_sup_right hz)) (Ideal.mem_sup_right ?_)
      rwa [pow_two] at h2
    have hall : ∀ y : m.Cotangent ⧸ N', ∃ z : m, (z : A) ∈ J ∧ p z = y := by
      intro y
      have hy : y ∈ Submodule.span (A ⧸ m) (Set.range b) := by rw [b.span_eq]; trivial
      induction hy using Submodule.span_induction with
      | mem y h =>
        obtain ⟨j, rfl⟩ := h
        exact ⟨v (b j), Ideal.mem_sup_left (Ideal.mem_sup_left (hu j)), hv _⟩
      | zero => exact ⟨0, zero_mem _, by simp [p]⟩
      | add y y' _ _ h h' =>
        obtain ⟨z, hz, rfl⟩ := h
        obtain ⟨z', hz', rfl⟩ := h'
        exact ⟨z + z', add_mem hz hz', hpadd _ _⟩
      | smul c y _ h =>
        obtain ⟨z, hz, rfl⟩ := h
        obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
        exact ⟨c • z, Ideal.mul_mem_left _ _ hz, hpsmul _ _⟩
    intro a ha
    obtain ⟨z, hz, hp⟩ := hall (p ⟨a, ha⟩)
    have h3 := hk _ ((Submodule.Quotient.eq N').mp hp.symm) (⟨a, ha⟩ - z) (map_sub _ _ _)
    have : a = (a - z) + z := by ring
    rw [this]
    exact add_mem h3 hz
  obtain ⟨c, hc, hcle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (IsNoetherian.noetherian m) le_rfl hle
  refine ⟨u, c, fun h => hmax.ne_top ?_, fun i => ?_, fun a ha => ?_⟩
  · rw [Ideal.eq_top_iff_one]
    have := sub_mem h hc
    rwa [sub_sub_cancel] at this
  · simp only [u]
    split_ifs
    · exact Subtype.prop _
    · exact zero_mem _
  · exact hcle (Submodule.smul_mem_pointwise_smul a c m ha)
end GlobalTheory.LocalCoord
