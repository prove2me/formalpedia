-- Prove2me | solution 1 for NumberField.AdeleRing.free_of_pi_linearEquiv_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/43071d12-9ead-5989-b887-fa3b32d911c3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdeleRing_free_of_pi_linearEquiv_pi

set_option autoImplicit false

open NumberField

namespace R4H2F

open Matrix

section Defs

def SplitsIdem (R : Type*) [CommRing R] : Prop :=
  ∀ (N m n : ℕ), 0 < n → ∀ (ε : Matrix (Fin N) (Fin N) R)
    (A' : Matrix (Fin (m * n)) (Fin N × Fin n) R) (B' : Matrix (Fin N × Fin n) (Fin (m * n)) R),
    ε * ε = ε → A' * B' = 1 → B' * A' = Matrix.blockDiagonal (fun _ : Fin n => ε) →
    ∃ (A : Matrix (Fin m) (Fin N) R) (B : Matrix (Fin N) (Fin m) R), A * B = 1 ∧ B * A = ε

end Defs

section Local

variable {R : Type*} [CommRing R]

theorem exists_splitting_of_isLocalRing [IsLocalRing R] {N : ℕ}
    (ε : Matrix (Fin N) (Fin N) R) (hε : ε * ε = ε) :
    ∃ (r : ℕ) (A : Matrix (Fin r) (Fin N) R) (B : Matrix (Fin N) (Fin r) R),
      A * B = 1 ∧ B * A = ε := by
  classical
  set e : (Fin N → R) →ₗ[R] (Fin N → R) := Matrix.toLin' ε with he_def
  have he : e ∘ₗ e = e := by rw [he_def, ← Matrix.toLin'_mul, hε]
  set M : Submodule R (Fin N → R) := LinearMap.range e with hM_def
  let p : (Fin N → R) →ₗ[R] M := e.rangeRestrict
  let s : M →ₗ[R] (Fin N → R) := M.subtype
  have hsp : s ∘ₗ p = e := by
    ext x i
    simp [s, p]
  have hps : p ∘ₗ s = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
    apply Subtype.ext
    change e (e y) = e y
    exact congrArg (fun f : (Fin N → R) →ₗ[R] (Fin N → R) => f y) he
  haveI : Module.Finite R M := inferInstance
  haveI : Module.Projective R M := Module.Projective.of_split s p hps
  haveI : Module.Free R M := Module.free_of_flat_of_isLocalRing
  set r := Module.finrank R M
  let b : Module.Basis (Fin r) R M := Module.finBasis R M
  refine ⟨r, LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ p),
    LinearMap.toMatrix' (s ∘ₗ b.equivFun.symm.toLinearMap), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc _ s p, hps, LinearMap.id_comp]
    ext x i
    simp
  · rw [← LinearMap.toMatrix'_comp]
    have hε' : LinearMap.toMatrix' e = ε := by rw [he_def, LinearMap.toMatrix'_toLin']
    rw [← hε']
    congr 1
    rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc p _ _]
    have : b.equivFun.symm.toLinearMap ∘ₗ b.equivFun.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [this, LinearMap.id_comp, hsp]

theorem trace_eq_of_splitting {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    {ε : Matrix ι ι R} {A : Matrix (Fin r) ι R} {B : Matrix ι (Fin r) R}
    (hAB : A * B = 1) (hBA : B * A = ε) : ε.trace = r := by
  rw [← hBA, Matrix.trace_mul_comm, hAB, Matrix.trace_one, Fintype.card_fin]

theorem splitsIdem_of_isLocalRing (R : Type*) [CommRing R] [IsLocalRing R] [CharZero R] :
    SplitsIdem R := by
  intro N m n hn ε A' B' hε hA'B' hB'A'
  classical
  obtain ⟨r, A, B, hAB, hBA⟩ := exists_splitting_of_isLocalRing ε hε
  have h1 : ε.trace = r := trace_eq_of_splitting hAB hBA
  have h2 : (Matrix.blockDiagonal (fun _ : Fin n => ε)).trace = (m * n : ℕ) := by
    rw [← hB'A', Matrix.trace_mul_comm, hA'B', Matrix.trace_one, Fintype.card_fin]
  rw [Matrix.trace_blockDiagonal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, h1,
    nsmul_eq_mul] at h2
  have h3 : n * r = m * n := by exact_mod_cast h2
  have hr : r = m := by
    rw [mul_comm] at h3
    exact Nat.eq_of_mul_eq_mul_right hn h3
  subst hr
  exact ⟨A, B, hAB, hBA⟩

end Local

section Transfer

variable {R S : Type*} [CommRing R] [CommRing S]

theorem hyps_map (φ : R →+* S) {N m n : ℕ} {ε : Matrix (Fin N) (Fin N) R}
    {A' : Matrix (Fin (m * n)) (Fin N × Fin n) R} {B' : Matrix (Fin N × Fin n) (Fin (m * n)) R}
    (hε : ε * ε = ε) (hA'B' : A' * B' = 1)
    (hB'A' : B' * A' = Matrix.blockDiagonal (fun _ : Fin n => ε)) :
    ε.map φ * ε.map φ = ε.map φ ∧ A'.map φ * B'.map φ = 1 ∧
      B'.map φ * A'.map φ = Matrix.blockDiagonal (fun _ : Fin n => ε.map φ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, hε]
  · rw [← Matrix.map_mul, hA'B', Matrix.map_one _ (map_zero φ) (map_one φ)]
  · rw [← Matrix.map_mul, hB'A', Matrix.blockDiagonal_map _ _ (map_zero φ)]

end Transfer

section Pi

theorem matrix_eq_of_map_eval_eq {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]
    {α β : Type*} {M M' : Matrix α β (∀ i, R i)}
    (h : ∀ i, M.map (Pi.evalRingHom R i) = M'.map (Pi.evalRingHom R i)) : M = M' :=
  Matrix.ext fun a b => funext fun i => congrFun (congrFun (h i) a) b

theorem splitsIdem_pi {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)]
    (h : ∀ i, SplitsIdem (R i)) : SplitsIdem (∀ i, R i) := by
  intro N m n hn ε A' B' hε hA'B' hB'A'
  have H : ∀ i, ∃ (A : Matrix (Fin m) (Fin N) (R i)) (B : Matrix (Fin N) (Fin m) (R i)),
      A * B = 1 ∧ B * A = ε.map (Pi.evalRingHom R i) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hyps_map (Pi.evalRingHom R i) hε hA'B' hB'A'
    exact h i N m n hn _ _ _ h1 h2 h3
  choose A B hAB hBA using H
  have hA : ∀ i, (Matrix.of fun a b i => A i a b).map (Pi.evalRingHom R i) = A i :=
    fun i => by ext a b; rfl
  have hB : ∀ i, (Matrix.of fun a b i => B i a b).map (Pi.evalRingHom R i) = B i :=
    fun i => by ext a b; rfl
  refine ⟨Matrix.of fun a b i => A i a b, Matrix.of fun a b i => B i a b, ?_, ?_⟩
  · refine matrix_eq_of_map_eval_eq fun i => ?_
    rw [Matrix.map_mul, hA, hB, hAB, Matrix.map_one _ (map_zero _) (map_one _)]
  · refine matrix_eq_of_map_eval_eq fun i => ?_
    rw [Matrix.map_mul, hA, hB, hBA]

theorem matrix_eq_of_map_fst_snd_eq {R S : Type*} [CommRing R] [CommRing S]
    {α β : Type*} {M M' : Matrix α β (R × S)}
    (h₁ : M.map (RingHom.fst R S) = M'.map (RingHom.fst R S))
    (h₂ : M.map (RingHom.snd R S) = M'.map (RingHom.snd R S)) : M = M' :=
  Matrix.ext fun a b => Prod.ext (congrFun (congrFun h₁ a) b) (congrFun (congrFun h₂ a) b)

theorem splitsIdem_prod (R S : Type*) [CommRing R] [CommRing S]
    (hR : SplitsIdem R) (hS : SplitsIdem S) : SplitsIdem (R × S) := by
  intro N m n hn ε A' B' hε hA'B' hB'A'
  obtain ⟨h1, h2, h3⟩ := hyps_map (RingHom.fst R S) hε hA'B' hB'A'
  obtain ⟨A₁, B₁, hAB₁, hBA₁⟩ := hR N m n hn _ _ _ h1 h2 h3
  obtain ⟨k1, k2, k3⟩ := hyps_map (RingHom.snd R S) hε hA'B' hB'A'
  obtain ⟨A₂, B₂, hAB₂, hBA₂⟩ := hS N m n hn _ _ _ k1 k2 k3
  have hA1 : (Matrix.of fun a b => (A₁ a b, A₂ a b)).map (RingHom.fst R S) = A₁ := by
    ext a b; rfl
  have hA2 : (Matrix.of fun a b => (A₁ a b, A₂ a b)).map (RingHom.snd R S) = A₂ := by
    ext a b; rfl
  have hB1 : (Matrix.of fun a b => (B₁ a b, B₂ a b)).map (RingHom.fst R S) = B₁ := by
    ext a b; rfl
  have hB2 : (Matrix.of fun a b => (B₁ a b, B₂ a b)).map (RingHom.snd R S) = B₂ := by
    ext a b; rfl
  refine ⟨Matrix.of fun a b => (A₁ a b, A₂ a b), Matrix.of fun a b => (B₁ a b, B₂ a b), ?_, ?_⟩
  · refine matrix_eq_of_map_fst_snd_eq ?_ ?_
    · rw [Matrix.map_mul, hA1, hB1, hAB₁, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [Matrix.map_mul, hA2, hB2, hAB₂, Matrix.map_one _ (map_zero _) (map_one _)]
  · refine matrix_eq_of_map_fst_snd_eq ?_ ?_
    · rw [Matrix.map_mul, hA1, hB1, hBA₁]
    · rw [Matrix.map_mul, hA2, hB2, hBA₂]

end Pi

section Restricted

open scoped RestrictedProduct
open Filter

variable {ι : Type*} {R : ι → Type*} [∀ i, CommRing (R i)]
variable {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubringClass (S i) (R i)]
variable {B : ∀ i, S i}

theorem exists_map_subtype_eq {α β : Type*} (i : ι) (M : Matrix α β (R i))
    (hM : ∀ a b, M a b ∈ B i) :
    ∃ M₀ : Matrix α β (B i), M₀.map (SubringClass.subtype (B i)) = M :=
  ⟨Matrix.of fun a b => ⟨M a b, hM a b⟩, by ext a b; rfl⟩

theorem matrix_eq_of_map_evalRingHom_eq {α β : Type*} {M M' : Matrix α β (Πʳ i, [R i, B i])}
    (h : ∀ i, M.map (RestrictedProduct.evalRingHom R i) =
      M'.map (RestrictedProduct.evalRingHom R i)) : M = M' :=
  Matrix.ext fun a b => RestrictedProduct.ext _ _ fun i => congrFun (congrFun (h i) a) b

theorem splitsIdem_restrictedProduct
    (hR : ∀ i, SplitsIdem (R i)) (hB : ∀ i, SplitsIdem (B i)) :
    SplitsIdem (Πʳ i, [R i, B i]) := by
  intro N m n hn ε A' B' hε hA'B' hB'A'
  classical

  let good : ι → Prop := fun i =>
    (∀ a b, ε a b i ∈ B i) ∧ (∀ a b, A' a b i ∈ B i) ∧ (∀ a b, B' a b i ∈ B i)
  have hgood : ∀ᶠ i in cofinite, good i := by
    refine (Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (ε a b).2).and
      ((Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (A' a b).2).and
        (Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (B' a b).2))
  let φ : ∀ i, (Πʳ i, [R i, B i]) →+* R i := fun i => RestrictedProduct.evalRingHom R i
  have H : ∀ i, ∃ (A : Matrix (Fin m) (Fin N) (R i)) (Bm : Matrix (Fin N) (Fin m) (R i)),
      A * Bm = 1 ∧ Bm * A = ε.map (φ i) ∧
        (good i → (∀ a b, A a b ∈ B i) ∧ (∀ a b, Bm a b ∈ B i)) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hyps_map (φ i) hε hA'B' hB'A'
    by_cases hg : good i
    · obtain ⟨hgε, hgA, hgB⟩ := hg
      obtain ⟨ε₀, hε₀⟩ := exists_map_subtype_eq (B := B) i (ε.map (φ i)) (fun a b => hgε a b)
      obtain ⟨A₀, hA₀⟩ := exists_map_subtype_eq (B := B) i (A'.map (φ i)) (fun a b => hgA a b)
      obtain ⟨B₀, hB₀⟩ := exists_map_subtype_eq (B := B) i (B'.map (φ i)) (fun a b => hgB a b)
      have hinj : Function.Injective
          (fun M : Matrix (Fin N) (Fin N) (B i) => M.map (SubringClass.subtype (B i))) :=
        fun _ _ h => Matrix.map_injective Subtype.val_injective h
      have hinj₁ : Function.Injective
          (fun M : Matrix (Fin (m * n)) (Fin (m * n)) (B i) =>
            M.map (SubringClass.subtype (B i))) :=
        fun _ _ h => Matrix.map_injective Subtype.val_injective h
      have hinj₂ : Function.Injective
          (fun M : Matrix (Fin N × Fin n) (Fin N × Fin n) (B i) =>
            M.map (SubringClass.subtype (B i))) :=
        fun _ _ h => Matrix.map_injective Subtype.val_injective h
      have e1 : ε₀ * ε₀ = ε₀ := hinj (by simp only [Matrix.map_mul, hε₀, h1])
      have e2 : A₀ * B₀ = 1 := hinj₁ (by
        simp only [Matrix.map_mul, hA₀, hB₀, h2]
        rw [Matrix.map_one _ (map_zero _) (map_one _)])
      have e3 : B₀ * A₀ = Matrix.blockDiagonal (fun _ : Fin n => ε₀) := hinj₂ (by
        simp only [Matrix.map_mul, hA₀, hB₀, h3]
        rw [Matrix.blockDiagonal_map _ _ (map_zero _), hε₀])
      obtain ⟨A, Bm, hAB, hBA⟩ := hB i N m n hn ε₀ A₀ B₀ e1 e2 e3
      refine ⟨A.map (SubringClass.subtype (B i)), Bm.map (SubringClass.subtype (B i)), ?_, ?_,
        fun _ => ⟨fun a b => (A a b).2, fun a b => (Bm a b).2⟩⟩
      · rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]
      · rw [← Matrix.map_mul, hBA, hε₀]
    · obtain ⟨A, Bm, hAB, hBA⟩ := hR i N m n hn _ _ _ h1 h2 h3
      exact ⟨A, Bm, hAB, hBA, fun hg' => absurd hg' hg⟩
  choose A Bm hAB hBA hint using H

  let Ag : Matrix (Fin m) (Fin N) (Πʳ i, [R i, B i]) := Matrix.of fun a b =>
    RestrictedProduct.mk (fun i => A i a b) (hgood.mono fun i hi => (hint i hi).1 a b)
  let Bg : Matrix (Fin N) (Fin m) (Πʳ i, [R i, B i]) := Matrix.of fun a b =>
    RestrictedProduct.mk (fun i => Bm i a b) (hgood.mono fun i hi => (hint i hi).2 a b)
  have hA : ∀ i, Ag.map (φ i) = A i := fun i => by ext a b; rfl
  have hBg : ∀ i, Bg.map (φ i) = Bm i := fun i => by ext a b; rfl
  refine ⟨Ag, Bg, ?_, ?_⟩
  · refine matrix_eq_of_map_evalRingHom_eq fun i => ?_
    change (Ag * Bg).map (φ i) = (1 : Matrix (Fin m) (Fin m) _).map (φ i)
    rw [Matrix.map_mul, hA, hBg, hAB, Matrix.map_one _ (map_zero _) (map_one _)]
  · refine matrix_eq_of_map_evalRingHom_eq fun i => ?_
    change (Bg * Ag).map (φ i) = ε.map (φ i)
    rw [Matrix.map_mul, hA, hBg, hBA]

end Restricted

section Reduction

variable {R : Type*} [CommRing R]

theorem free_of_splitsIdem (hR : SplitsIdem R) {m n : ℕ} (hn : 0 < n)
    {P : Type*} [AddCommGroup P] [Module R P]
    (f : (Fin n → P) ≃ₗ[R] (Fin (m * n) → R)) : Module.Free R P := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  let ι : P →ₗ[R] (Fin n → P) := LinearMap.single R (fun _ : Fin n => P) i0
  let π : (Fin n → P) →ₗ[R] P := LinearMap.proj i0
  let s : P →ₗ[R] (Fin (m * n) → R) := f.toLinearMap ∘ₗ ι
  let p : (Fin (m * n) → R) →ₗ[R] P := π ∘ₗ f.symm.toLinearMap
  have hps : ∀ x, p (s x) = x := fun x => by simp [p, s, π, ι, i0]
  let e : (Fin (m * n) → R) →ₗ[R] (Fin (m * n) → R) := s ∘ₗ p
  have he : ∀ y, e y = s (p y) := fun y => rfl
  let ε : Matrix (Fin (m * n)) (Fin (m * n)) R := LinearMap.toMatrix' e
  have hεe : Matrix.toLin' ε = e := Matrix.toLin'_toMatrix' e
  have hε : ε * ε = ε := by
    change LinearMap.toMatrix' e * LinearMap.toMatrix' e = LinearMap.toMatrix' e
    rw [← LinearMap.toMatrix'_comp]
    congr 1
    exact LinearMap.ext fun y => by simp only [LinearMap.comp_apply, he, hps]

  let Ψ : (Fin n → P) →ₗ[R] (Fin (m * n) × Fin n → R) :=
    LinearMap.pi fun ki => (LinearMap.proj ki.1 ∘ₗ s) ∘ₗ LinearMap.proj ki.2
  let Φ : (Fin (m * n) × Fin n → R) →ₗ[R] (Fin n → P) :=
    LinearMap.pi fun i => p ∘ₗ LinearMap.pi fun k => LinearMap.proj (k, i)
  have hΨ : ∀ x ki, Ψ x ki = s (x ki.2) ki.1 := fun x ki => rfl
  have hΦ : ∀ y i, Φ y i = p (fun k => y (k, i)) := fun y i => rfl
  have hΦΨ : ∀ x, Φ (Ψ x) = x := fun x => by
    funext i
    rw [hΦ]
    exact hps (x i)
  let A' : Matrix (Fin (m * n)) (Fin (m * n) × Fin n) R :=
    LinearMap.toMatrix' (f.toLinearMap ∘ₗ Φ)
  let B' : Matrix (Fin (m * n) × Fin n) (Fin (m * n)) R :=
    LinearMap.toMatrix' (Ψ ∘ₗ f.symm.toLinearMap)
  have hA'B' : A' * B' = 1 := by
    change LinearMap.toMatrix' _ * LinearMap.toMatrix' _ = 1
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply, hΦΨ,
      LinearEquiv.apply_symm_apply]
  have hB'A' : B' * A' = Matrix.blockDiagonal (fun _ : Fin n => ε) := by
    change LinearMap.toMatrix' _ * LinearMap.toMatrix' _ = _
    rw [← LinearMap.toMatrix'_comp]
    ext ⟨k, i⟩ ⟨k', i'⟩
    rw [LinearMap.toMatrix'_apply, Matrix.blockDiagonal_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, hΨ, hΦ]
    by_cases hii : i = i'
    · subst hii
      rw [if_pos rfl]
      change _ = LinearMap.toMatrix' e k k'
      rw [LinearMap.toMatrix'_apply, he]
      have h1 : (fun k'' : Fin (m * n) => (Pi.single (k', i) (1 : R) :
          Fin (m * n) × Fin n → R) (k'', i)) = Pi.single k' 1 := by
        funext k''
        simp [Pi.single_apply]
      rw [h1]
    · rw [if_neg hii]
      have h0 : (fun k'' : Fin (m * n) => (Pi.single (k', i') (1 : R) :
          Fin (m * n) × Fin n → R) (k'', i)) = 0 := by
        funext k''
        simp [hii]
      rw [h0, map_zero, map_zero, Pi.zero_apply]
  obtain ⟨A, B, hAB, hBA⟩ := hR (m * n) m n hn ε A' B' hε hA'B' hB'A'

  have hAεB : A * ε * B = 1 := by
    rw [← hBA, ← Matrix.mul_assoc, hAB, Matrix.one_mul, hAB]
  let u : P →ₗ[R] (Fin m → R) := Matrix.toLin' A ∘ₗ s
  let w : (Fin m → R) →ₗ[R] P := p ∘ₗ Matrix.toLin' B
  have hwu : w ∘ₗ u = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    simp only [u, w, LinearMap.comp_apply, LinearMap.id_apply]
    rw [← Matrix.toLin'_mul_apply, hBA, hεe, he, hps, hps]
  have huw : u ∘ₗ w = LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    simp only [u, w, LinearMap.comp_apply, LinearMap.id_apply]
    rw [← he, ← hεe, ← Matrix.toLin'_mul_apply, ← Matrix.toLin'_mul_apply, hAεB,
      Matrix.toLin'_one, LinearMap.id_apply]
  exact Module.Free.of_equiv (LinearEquiv.ofLinear u w huw hwu).symm

end Reduction

section Adelic

open IsDedekindDomain

variable (F : Type*) [Field F] [NumberField F]

theorem charZero_completion (v : InfinitePlace F) : CharZero v.Completion :=
  charZero_of_injective_algebraMap (algebraMap F v.Completion).injective

theorem charZero_adicCompletion (v : HeightOneSpectrum (𝓞 F)) : CharZero (v.adicCompletion F) :=
  charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective

theorem charZero_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    CharZero (v.adicCompletionIntegers F) :=
  haveI := charZero_adicCompletion F v
  (v.adicCompletionIntegers F).subtype.charZero

theorem splitsIdem_infiniteAdeleRing : SplitsIdem (InfiniteAdeleRing F) :=
  splitsIdem_pi (fun v : InfinitePlace F => v.Completion) fun v =>
    haveI := charZero_completion F v
    splitsIdem_of_isLocalRing _

theorem splitsIdem_finiteAdeleRing : SplitsIdem (FiniteAdeleRing (𝓞 F) F) :=
  splitsIdem_restrictedProduct (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (B := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
    (fun v =>
      haveI := charZero_adicCompletion F v
      splitsIdem_of_isLocalRing _)
    (fun v =>
      haveI := charZero_adicCompletionIntegers F v
      splitsIdem_of_isLocalRing _)

theorem splitsIdem_adeleRing : SplitsIdem (AdeleRing (𝓞 F) F) :=
  splitsIdem_prod _ _ (splitsIdem_infiniteAdeleRing F) (splitsIdem_finiteAdeleRing F)

end Adelic

end R4H2F

theorem solution
    (F : Type) [Field F] [NumberField F] (m n : ℕ) (hn : 0 < n)
    (P : Type) [AddCommGroup P] [Module (AdeleRing (𝓞 F) F) P]
    (f : (Fin n → P) ≃ₗ[AdeleRing (𝓞 F) F] (Fin (m * n) → AdeleRing (𝓞 F) F)) :
    Module.Free (AdeleRing (𝓞 F) F) P :=
  R4H2F.free_of_splitsIdem (R4H2F.splitsIdem_adeleRing F) hn f

end S_NumberField_AdeleRing_free_of_pi_linearEquiv_pi
end P2MW
export P2MW.S_NumberField_AdeleRing_free_of_pi_linearEquiv_pi (solution)
