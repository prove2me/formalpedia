-- Prove2me | solution 1 for MvFormalGroup.existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural_of_mem_radical
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/87cb8295-c673-5cec-b6e5-5d5fb9b68bed

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural_of_mem_radical

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map mk toPowerSeries adicEval adicEval_X adicEvalAlgHom coe_adicEvalAlgHom map_adicEval existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural"
namespace RadicalLaw
p2m_open "MvFormalGroup"

section PClass

variable {A : Type*} [CommRing A] (p : ℕ)

theorem mem_pow_smul_top_iff {x : A} {n : ℕ} :
    x ∈ (Ideal.span {(p : A)}) ^ n • (⊤ : Submodule A A) ↔ ∃ y, x = (p : A) ^ n * y := by
  rw [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton']
  exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [← hy, mul_comm]⟩, fun ⟨y, hy⟩ => ⟨y, by rw [hy, mul_comm]⟩⟩

variable {B : Type*} [CommRing B] [Algebra A B] {ι : Type*} (e : B ≃ₗ[A] (ι → A))

variable (A) in
theorem natCast_pow_mul_eq_smul (n : ℕ) (y : B) : (p : B) ^ n * y = ((p : A) ^ n) • y := by
  rw [Algebra.smul_def, map_pow, map_natCast]

include e in

theorem mem_pow_smul_top_iff_coord {x : B} {n : ℕ} :
    x ∈ (Ideal.span {(p : B)}) ^ n • (⊤ : Submodule B B) ↔
      ∀ i, e x i ∈ (Ideal.span {(p : A)}) ^ n • (⊤ : Submodule A A) := by
  rw [mem_pow_smul_top_iff]
  simp only [mem_pow_smul_top_iff]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨e y i, by rw [natCast_pow_mul_eq_smul A, map_smul, Pi.smul_apply, smul_eq_mul]⟩
  · intro h
    choose c hc using h
    refine ⟨e.symm c, ?_⟩
    apply e.injective
    rw [natCast_pow_mul_eq_smul A, map_smul, e.apply_symm_apply]
    funext i
    rw [Pi.smul_apply, smul_eq_mul, hc i]

include e in

theorem mem_nonZeroDivisors_of_equiv (hp : (p : A) ∈ nonZeroDivisors A) :
    (p : B) ∈ nonZeroDivisors B := by
  refine mem_nonZeroDivisors_iff_right.2 fun x hx => ?_
  have hx' : (p : A) • x = 0 := by
    rw [Algebra.smul_def, map_natCast, mul_comm]
    exact hx
  apply e.injective
  rw [map_zero]
  funext i
  have hi : (p : A) * e x i = 0 := by
    rw [← smul_eq_mul, ← Pi.smul_apply, ← map_smul, hx', map_zero, Pi.zero_apply]
  exact mem_nonZeroDivisors_iff_right.1 hp _ (by rw [mul_comm]; exact hi)

include e in

theorem isAdicComplete_of_equiv [IsAdicComplete (Ideal.span {(p : A)}) A] :
    IsAdicComplete (Ideal.span {(p : B)}) B := by
  have hH : IsHausdorff (Ideal.span {(p : B)}) B := by
    refine ⟨fun x hx => ?_⟩
    apply e.injective
    rw [map_zero]
    funext i
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : A)}) A) _ fun n => ?_
    rw [SModEq.zero]
    exact (mem_pow_smul_top_iff_coord p e).1 (SModEq.zero.1 (hx n)) i
  have hP : IsPrecomplete (Ideal.span {(p : B)}) B := by
    refine ⟨fun {f} hf => ?_⟩
    have hcoord : ∀ i, ∃ L : A, ∀ n, e (f n) i ≡ L [SMOD (Ideal.span {(p : A)}) ^ n • (⊤ : Submodule A A)] := by
      intro i
      refine IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {(p : A)}) A) fun {m n} hmn => ?_
      rw [SModEq.sub_mem, ← Pi.sub_apply, ← map_sub]
      exact (mem_pow_smul_top_iff_coord p e).1 (SModEq.sub_mem.1 (hf hmn)) i
    choose L hL using hcoord
    refine ⟨e.symm L, fun n => ?_⟩
    rw [SModEq.sub_mem, mem_pow_smul_top_iff_coord p e]
    intro i
    rw [map_sub, e.apply_symm_apply, Pi.sub_apply]
    exact SModEq.sub_mem.1 (hL i n)
  exact @IsAdicComplete.mk _ _ _ _ _ _ hH hP

end PClass

section Trunc

variable (σ : Type*) (R : Type*) [CommRing R]

def truncIdeal (N : ℕ) : Ideal (MvPolynomial σ R) where
  carrier := {f | ∀ m : σ →₀ ℕ, m.degree < N → MvPolynomial.coeff m f = 0}
  zero_mem' := fun m _ => MvPolynomial.coeff_zero m
  add_mem' := fun {f g} hf hg m hm => by
    rw [MvPolynomial.coeff_add, hf m hm, hg m hm, add_zero]
  smul_mem' := fun h f hf m hm => by
    classical
    rw [smul_eq_mul, MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hle : x.2.degree ≤ m.degree := by
      rw [← hx, map_add]
      exact le_add_self
    rw [hf x.2 (lt_of_le_of_lt hle hm), mul_zero]

abbrev TruncAlg (N : ℕ) : Type _ := MvPolynomial σ R ⧸ truncIdeal σ R N

def DegLT (N : ℕ) : Type _ := {m : σ →₀ ℕ // m.degree < N}

scoped instance instFiniteDegLT [Finite σ] (N : ℕ) : Finite (DegLT σ N) :=
  (Finsupp.finite_of_degree_lt (σ := σ) N).to_subtype

variable {σ R}

theorem mem_truncIdeal {N : ℕ} {f : MvPolynomial σ R} :
    f ∈ truncIdeal σ R N ↔ ∀ m : σ →₀ ℕ, m.degree < N → MvPolynomial.coeff m f = 0 :=
  Iff.rfl

def coeffsLT (N : ℕ) : MvPolynomial σ R →ₗ[R] (DegLT σ N → R) where
  toFun f m := MvPolynomial.coeff m.1 f
  map_add' f g := by
    funext m
    exact MvPolynomial.coeff_add m.1 f g
  map_smul' r f := by
    funext m
    rw [RingHom.id_apply, Pi.smul_apply, MvPolynomial.coeff_smul]

theorem coeffsLT_apply (N : ℕ) (f : MvPolynomial σ R) (m : DegLT σ N) :
    coeffsLT N f m = MvPolynomial.coeff m.1 f :=
  rfl

theorem ker_coeffsLT (N : ℕ) :
    LinearMap.ker (coeffsLT (σ := σ) (R := R) N) = (truncIdeal σ R N).restrictScalars R := by
  ext f
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, mem_truncIdeal]
  constructor
  · intro h m hm
    exact congrFun h ⟨m, hm⟩
  · intro h
    funext m
    exact h m.1 m.2

theorem coeffsLT_surjective [Finite σ] (N : ℕ) :
    Function.Surjective (coeffsLT (σ := σ) (R := R) N) := by
  classical
  haveI := Fintype.ofFinite (DegLT σ N)
  intro c
  refine ⟨∑ n : DegLT σ N, MvPolynomial.monomial n.1 (c n), ?_⟩
  funext m
  rw [coeffsLT_apply, MvPolynomial.coeff_sum, Finset.sum_eq_single m]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro n _ hnm
    rw [MvPolynomial.coeff_monomial, if_neg fun h => hnm (Subtype.ext h)]
  · intro h
    exact absurd (Finset.mem_univ m) h

private def coordAux₁ [Finite σ] (N : ℕ) :=
  LinearMap.quotKerEquivOfSurjective (coeffsLT (σ := σ) (R := R) N) (coeffsLT_surjective N)

private def coordAux₂ (N : ℕ) :=
  Submodule.quotEquivOfEq _ _ (ker_coeffsLT (σ := σ) (R := R) N).symm

private def coordAux₃ (N : ℕ) :=
  (Submodule.Quotient.restrictScalarsEquiv R (truncIdeal σ R N)).symm

private def coordAux₂₁ [Finite σ] (N : ℕ) := (coordAux₂ (σ := σ) (R := R) N) ≪≫ₗ (coordAux₁ N)

variable (σ R) in

def coord [Finite σ] (N : ℕ) : TruncAlg σ R N ≃ₗ[R] (DegLT σ N → R) :=
  (coordAux₃ (σ := σ) (R := R) N) ≪≫ₗ (coordAux₂₁ N)

theorem coord_mk [Finite σ] (N : ℕ) (f : MvPolynomial σ R) (m : DegLT σ N) :
    coord σ R N (Ideal.Quotient.mk (truncIdeal σ R N) f) m = MvPolynomial.coeff m.1 f :=
  rfl

scoped instance instFree [Finite σ] (N : ℕ) : Module.Free R (TruncAlg σ R N) :=
  Module.Free.of_equiv (coord σ R N).symm

scoped instance instFinite [Finite σ] (N : ℕ) : Module.Finite R (TruncAlg σ R N) :=
  Module.Finite.equiv (coord σ R N).symm

variable (R) in

abbrev tX (N : ℕ) (s : σ) : TruncAlg σ R N := Ideal.Quotient.mk _ (MvPolynomial.X s)

theorem mk_eq_mk_iff {N : ℕ} {f g : MvPolynomial σ R} :
    Ideal.Quotient.mk (truncIdeal σ R N) f = Ideal.Quotient.mk _ g ↔
      ∀ m : σ →₀ ℕ, m.degree < N → MvPolynomial.coeff m f = MvPolynomial.coeff m g := by
  rw [Ideal.Quotient.eq, mem_truncIdeal]
  simp only [MvPolynomial.coeff_sub, sub_eq_zero]

theorem monomial_mem_truncIdeal {N : ℕ} {m : σ →₀ ℕ} (hm : N ≤ m.degree) (r : R) :
    MvPolynomial.monomial m r ∈ truncIdeal σ R N := fun n hn => by
  classical
  rw [MvPolynomial.coeff_monomial, if_neg]
  rintro rfl
  exact absurd hm (not_le.2 hn)

theorem prod_tX_pow_eq_zero {N : ℕ} {m : σ →₀ ℕ} (hm : N ≤ m.degree) :
    m.prod (fun s e => (tX R N s) ^ e) = 0 := by
  have h : m.prod (fun s e => (tX R N s) ^ e) =
      Ideal.Quotient.mk _ (m.prod fun s e => (MvPolynomial.X s : MvPolynomial σ R) ^ e) := by
    rw [map_finsuppProd]
    simp only [map_pow]
  rw [h, Finsupp.prod, MvPolynomial.prod_X_pow_eq_monomial, Ideal.Quotient.eq_zero_iff_mem]
  exact monomial_mem_truncIdeal hm 1

theorem isNilpotent_tX (N : ℕ) (s : σ) : IsNilpotent (tX R N s) := by
  refine ⟨N, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.X_pow_eq_monomial]
  exact monomial_mem_truncIdeal (le_of_eq (Finsupp.degree_single _ _).symm) 1

theorem aeval_tX (N : ℕ) (f : MvPolynomial σ R) :
    MvPolynomial.aeval (tX R N) f = Ideal.Quotient.mk (truncIdeal σ R N) f := by
  have h := MvPolynomial.comp_aeval (MvPolynomial.X (R := R) (σ := σ))
    (Ideal.Quotient.mkₐ R (truncIdeal σ R N))
  rw [MvPolynomial.aeval_X_left, AlgHom.comp_id] at h
  exact (DFunLike.congr_fun h f).symm

variable {S : Type*} [CommRing S] [Algebra R S]

theorem aeval_eq_zero_of_mem_truncIdeal {N : ℕ} {w : σ → S}
    (hw : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => w s ^ e) = 0)
    {f : MvPolynomial σ R} (hf : f ∈ truncIdeal σ R N) : MvPolynomial.aeval w f = 0 := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : m.degree < N
  · rw [hf m hm, map_zero, zero_mul]
  · rw [show (∏ i ∈ m.support, w i ^ m i) = m.prod (fun s e => w s ^ e) from rfl,
      hw m (not_lt.1 hm), mul_zero]

private noncomputable def _root_.MvFormalGroup.RadicalLaw.lift (N : ℕ) (w : σ → S)
    (hw : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => w s ^ e) = 0) :
    TruncAlg σ R N →ₐ[R] S :=
  Ideal.Quotient.liftₐ (truncIdeal σ R N) (MvPolynomial.aeval w)
    (fun _ hf => aeval_eq_zero_of_mem_truncIdeal hw hf)

p2m_export "MvFormalGroup.RadicalLaw" "lift"
private theorem _root_.MvFormalGroup.RadicalLaw.lift_mk (N : ℕ) (w : σ → S)
    (hw : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => w s ^ e) = 0) (f : MvPolynomial σ R) :
    lift N w hw (Ideal.Quotient.mk _ f) = MvPolynomial.aeval w f :=
  rfl

p2m_export "MvFormalGroup.RadicalLaw" "lift_mk"
theorem lift_tX (N : ℕ) (w : σ → S)
    (hw : ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => w s ^ e) = 0) (s : σ) :
    lift N w hw (tX R N s) = w s := by
  rw [lift_mk, MvPolynomial.aeval_X]

end Trunc

section NilDegree

variable {S : Type*} [CommRing S] {σ : Type*}

theorem exists_forall_degree_le_prod_eq_zero_of_isNilpotent [Finite σ]
    (x : σ → S) (hx : ∀ s, IsNilpotent (x s)) :
    ∃ N : ℕ, ∀ m : σ →₀ ℕ, N ≤ m.degree → m.prod (fun s e => x s ^ e) = 0 := by
  classical
  haveI := Fintype.ofFinite σ
  choose k hk using hx
  refine ⟨∑ s, (k s + 1) + 1, fun m hm => ?_⟩

  have hlt : ∑ s, (k s + 1) < ∑ s, m s := by
    rw [← Finsupp.degree_eq_sum]; exact Nat.lt_of_succ_le hm
  obtain ⟨s, -, hs⟩ := Finset.exists_lt_of_sum_lt hlt
  have hms : s ∈ m.support := Finsupp.mem_support_iff.2 (by omega)
  refine Finset.prod_eq_zero hms ?_
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hs.le
  change x s ^ m s = 0
  rw [hr, pow_add, pow_succ, hk s, zero_mul, zero_mul]

end NilDegree

section ClassBasics

variable {S S' : Type*} [CommRing S] [CommRing S'] (p : ℕ)

theorem mem_radical_of_isNilpotent' {x : S} (hx : IsNilpotent x) (I : Ideal S) : x ∈ I.radical := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, hn ▸ I.zero_mem⟩

theorem map_mem_radical_of_mem_span {F : Type*} [FunLike F S S'] [RingHomClass F S S'] (φ : F)
    {s : S} (hs : s ∈ Ideal.span {(p : S)}) : φ s ∈ (Ideal.span {(p : S')}).radical := by
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hs
  refine Ideal.le_radical ?_
  rw [map_mul, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem map_mem_radical {F : Type*} [FunLike F S S'] [RingHomClass F S S'] (φ : F)
    {s : S} (hs : s ∈ (Ideal.span {(p : S)}).radical) : φ s ∈ (Ideal.span {(p : S')}).radical := by
  obtain ⟨n, hn⟩ := hs
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hn
  refine ⟨n, Ideal.mem_span_singleton'.2 ⟨φ t, ?_⟩⟩
  rw [← map_pow, ← ht, map_mul, map_natCast]

end ClassBasics

section Base

variable (𝓞 : Type u) [CommRing 𝓞] (p : ℕ) {d : ℕ}

variable {𝓞} in

theorem nzd_of_free (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (g : Type*) [CommRing g] [Algebra 𝓞 g]
    [Module.Free 𝓞 g] [Module.Finite 𝓞 g] : (p : g) ∈ nonZeroDivisors g :=
  mem_nonZeroDivisors_of_equiv p (Module.Free.chooseBasis 𝓞 g).equivFun hp

theorem isAdicComplete_of_free [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (g : Type*) [CommRing g] [Algebra 𝓞 g]
    [Module.Free 𝓞 g] [Module.Finite 𝓞 g] : IsAdicComplete (Ideal.span {(p : g)}) g :=
  isAdicComplete_of_equiv p (Module.Free.chooseBasis 𝓞 g).equivFun

variable {𝓞}
variable (μ : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (Fin d → g) → (Fin d → g) → (Fin d → g))

def NatHyp : Prop :=
  ∀ (g g' : Type u) [CommRing g] [Algebra 𝓞 g] [CommRing g'] [Algebra 𝓞 g'],
    (p : g) ∈ nonZeroDivisors g → IsAdicComplete (Ideal.span {(p : g)}) g →
    (p : g') ∈ nonZeroDivisors g' → IsAdicComplete (Ideal.span {(p : g')}) g' →
    ∀ (φ : g →ₐ[𝓞] g') (x y : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) →
      (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) → μ g' (φ ∘ x) (φ ∘ y) = φ ∘ μ g x y

def Good (Φ : MvFormalGroup d 𝓞) (g : Type u) [CommRing g] [Algebra 𝓞 g] (t : Fin d ⊕ Fin d → g) : Prop :=
  ∀ i, μ g (t ∘ Sum.inl) (t ∘ Sum.inr) i = adicEval (Ideal.span {(p : g)}) t (Φ.toPowerSeries i)

theorem good_of_isNilpotent [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (hnat : NatHyp p μ) (Φ : MvFormalGroup d 𝓞)
    (hΦ : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g] [Module.Free 𝓞 g] [Module.Finite 𝓞 g]
        (x y : Fin d → g), (∀ j, IsNilpotent (x j)) → (∀ j, IsNilpotent (y j)) →
        ∀ i, μ g x y i = adicEval (Ideal.span {(p : g)}) (Sum.elim x y) (Φ.toPowerSeries i))
    (g : Type u) [CommRing g] [Algebra 𝓞 g] (hg : (p : g) ∈ nonZeroDivisors g)
    (hgc : IsAdicComplete (Ideal.span {(p : g)}) g)
    (t : Fin d ⊕ Fin d → g) (ht : ∀ s, IsNilpotent (t s)) : Good p μ Φ g t := by
  intro i
  obtain ⟨N, hN⟩ := exists_forall_degree_le_prod_eq_zero_of_isNilpotent t ht
  haveI := hgc
  haveI : IsAdicComplete (Ideal.span {(p : TruncAlg (Fin d ⊕ Fin d) 𝓞 N)}) (TruncAlg (Fin d ⊕ Fin d) 𝓞 N) :=
    isAdicComplete_of_free 𝓞 p _
  let φ : TruncAlg (Fin d ⊕ Fin d) 𝓞 N →ₐ[𝓞] g := lift N t hN
  have hφ : ∀ s, φ (tX 𝓞 N s) = t s := fun s => lift_tX N t hN s
  have hX : ∀ s : Fin d ⊕ Fin d, IsNilpotent (tX 𝓞 N s) := fun s => isNilpotent_tX N s
  have key := hnat (TruncAlg (Fin d ⊕ Fin d) 𝓞 N) g (nzd_of_free p hp _) inferInstance hg hgc φ
    (fun j => tX 𝓞 N (Sum.inl j)) (fun j => tX 𝓞 N (Sum.inr j))
    (fun j => mem_radical_of_isNilpotent' (hX _) _) (fun j => mem_radical_of_isNilpotent' (hX _) _)
  have h1 := hΦ (TruncAlg (Fin d ⊕ Fin d) 𝓞 N) (fun j => tX 𝓞 N (Sum.inl j)) (fun j => tX 𝓞 N (Sum.inr j))
    (fun j => hX _) (fun j => hX _) i
  have hxl : (φ ∘ fun j => tX 𝓞 N (Sum.inl j)) = t ∘ Sum.inl := funext fun j => hφ _
  have hxr : (φ ∘ fun j => tX 𝓞 N (Sum.inr j)) = t ∘ Sum.inr := funext fun j => hφ _
  rw [hxl, hxr] at key
  have hsum : (fun s => φ (Sum.elim (fun j => tX 𝓞 N (Sum.inl j)) (fun j => tX 𝓞 N (Sum.inr j)) s)) = t := by
    funext s
    rcases s with j | j <;> exact hφ _
  rw [show μ g (t ∘ Sum.inl) (t ∘ Sum.inr) i = φ (μ _ _ _ i) from congrFun key i, h1,
    map_adicEval (Ideal.span {(p : TruncAlg (Fin d ⊕ Fin d) 𝓞 N)}) (Ideal.span {(p : g)}) φ
      (Submodule.fg_span_singleton _) (fun s hs => map_mem_radical_of_mem_span p φ hs)
      (fun s => by rcases s with j | j <;> exact mem_radical_of_isNilpotent' (hX _) _), hsum]

end Base

section Step

variable (𝓞 : Type u) [CommRing 𝓞] (g : Type u) [CommRing g] [Algebra 𝓞 g] (p : ℕ)

def coeffEquiv : PowerSeries g ≃ₗ[g] ((Unit →₀ ℕ) → g) := LinearEquiv.refl g (MvPowerSeries Unit g)

theorem nzd_powerSeries (hg : (p : g) ∈ nonZeroDivisors g) :
    (p : PowerSeries g) ∈ nonZeroDivisors (PowerSeries g) :=
  mem_nonZeroDivisors_of_equiv p (coeffEquiv g) hg

theorem isAdicComplete_powerSeries [IsAdicComplete (Ideal.span {(p : g)}) g] :
    IsAdicComplete (Ideal.span {(p : PowerSeries g)}) (PowerSeries g) :=
  isAdicComplete_of_equiv p (coeffEquiv g)

def thickPoly (n : ℕ) : Polynomial (PowerSeries g) :=
  Polynomial.X ^ n - Polynomial.C ((p : PowerSeries g) * PowerSeries.X)

theorem monic_thickPoly {n : ℕ} (hn : n ≠ 0) : (thickPoly g p n).Monic :=
  Polynomial.monic_X_pow_sub_C _ hn

abbrev Thick (n : ℕ) : Type u := AdjoinRoot (thickPoly g p n)

theorem root_pow (n : ℕ) : (AdjoinRoot.root (thickPoly g p n)) ^ n =
    (p : Thick g p n) * AdjoinRoot.of (thickPoly g p n) PowerSeries.X := by
  have h : Polynomial.eval₂ (AdjoinRoot.of (thickPoly g p n)) (AdjoinRoot.root (thickPoly g p n))
      (Polynomial.X ^ n - Polynomial.C ((p : PowerSeries g) * PowerSeries.X)) = 0 :=
    AdjoinRoot.eval₂_root _
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h
  simpa only [map_mul, map_natCast] using h

theorem root_mem_radical (n : ℕ) :
    AdjoinRoot.root (thickPoly g p n) ∈ (Ideal.span {(p : Thick g p n)}).radical :=
  ⟨n, by rw [root_pow]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)⟩

theorem nzd_thick {n : ℕ} (hn : n ≠ 0) (hg : (p : g) ∈ nonZeroDivisors g) :
    (p : Thick g p n) ∈ nonZeroDivisors (Thick g p n) :=
  mem_nonZeroDivisors_of_equiv p (A := PowerSeries g)
    (AdjoinRoot.powerBasis' (monic_thickPoly g p hn)).basis.equivFun (nzd_powerSeries g p hg)

theorem isAdicComplete_thick {n : ℕ} (hn : n ≠ 0) [IsAdicComplete (Ideal.span {(p : g)}) g] :
    IsAdicComplete (Ideal.span {(p : Thick g p n)}) (Thick g p n) :=
  haveI := isAdicComplete_powerSeries g p
  isAdicComplete_of_equiv p (A := PowerSeries g) (AdjoinRoot.powerBasis' (monic_thickPoly g p hn)).basis.equivFun

section Eval

variable {g} [IsAdicComplete (Ideal.span {(p : g)}) g]

def evalPS {v : g} (hv : v ∈ (Ideal.span {(p : g)}).radical) : PowerSeries g →ₐ[g] g :=
  adicEvalAlgHom (R := g) (σ := Unit) (Ideal.span {(p : g)}) (x := fun _ => v) (fun _ => hv)

theorem evalPS_X {v : g} (hv : v ∈ (Ideal.span {(p : g)}).radical) : evalPS p hv PowerSeries.X = v := by
  show adicEvalAlgHom (R := g) (σ := Unit) (Ideal.span {(p : g)}) (x := fun _ => v) (fun _ => hv)
    (MvPowerSeries.X () : MvPowerSeries Unit g) = v
  rw [coe_adicEvalAlgHom]
  exact adicEval_X _ _ _

theorem eval₂_thickPoly_eq_zero {v z : g} (hv : v ∈ (Ideal.span {(p : g)}).radical) {n : ℕ}
    (hz : z ^ n = p * v) : Polynomial.eval₂ (evalPS p hv).toRingHom z (thickPoly g p n) = 0 := by
  rw [thickPoly, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero, hz]
  show _ = (evalPS p hv) ((p : PowerSeries g) * PowerSeries.X)
  rw [map_mul, map_natCast, evalPS_X]

def thickEval {v z : g} (hv : v ∈ (Ideal.span {(p : g)}).radical) {n : ℕ} (hz : z ^ n = p * v) :
    Thick g p n →ₐ[𝓞] g where
  toRingHom := AdjoinRoot.lift (evalPS p hv).toRingHom z (eval₂_thickPoly_eq_zero p hv hz)
  commutes' o := by
    show AdjoinRoot.lift (evalPS p hv).toRingHom z _ (algebraMap 𝓞 (Thick g p n) o) = algebraMap 𝓞 g o
    rw [IsScalarTower.algebraMap_apply 𝓞 (PowerSeries g) (Thick g p n), AdjoinRoot.algebraMap_eq,
      AdjoinRoot.lift_of]
    show evalPS p hv (algebraMap 𝓞 (PowerSeries g) o) = _
    rw [IsScalarTower.algebraMap_apply 𝓞 g (PowerSeries g), AlgHom.commutes]
    rfl

theorem thickEval_root {v z : g} (hv : v ∈ (Ideal.span {(p : g)}).radical) {n : ℕ} (hz : z ^ n = p * v) :
    thickEval 𝓞 p hv hz (AdjoinRoot.root _) = z :=
  AdjoinRoot.lift_root (eval₂_thickPoly_eq_zero p hv hz)

theorem thickEval_of {v z : g} (hv : v ∈ (Ideal.span {(p : g)}).radical) {n : ℕ} (hz : z ^ n = p * v)
    (F : PowerSeries g) : thickEval 𝓞 p hv hz (AdjoinRoot.of _ F) = evalPS p hv F :=
  AdjoinRoot.lift_of (eval₂_thickPoly_eq_zero p hv hz)

theorem thickEval_algebraMap {v z : g} (hv : v ∈ (Ideal.span {(p : g)}).radical) {n : ℕ}
    (hz : z ^ n = p * v) (a : g) : thickEval 𝓞 p hv hz (algebraMap g (Thick g p n) a) = a := by
  rw [IsScalarTower.algebraMap_apply g (PowerSeries g) (Thick g p n), AdjoinRoot.algebraMap_eq, thickEval_of]
  exact (evalPS p hv).commutes a

end Eval

def truncI (M : ℕ) : Ideal (PowerSeries g) := Ideal.span {PowerSeries.X ^ (M + 1)}

abbrev TruncPS (M : ℕ) : Type u := PowerSeries g ⧸ truncI g M

theorem mem_truncI_iff {M : ℕ} {F : PowerSeries g} :
    F ∈ truncI g M ↔ ∀ m < M + 1, PowerSeries.coeff m F = 0 := by
  rw [truncI, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]

def truncCoeffs (M : ℕ) : PowerSeries g →ₗ[g] (Fin (M + 1) → g) :=
  LinearMap.pi fun i => PowerSeries.coeff (i : ℕ)

theorem truncCoeffs_apply (M : ℕ) (F : PowerSeries g) (i : Fin (M + 1)) :
    truncCoeffs g M F i = PowerSeries.coeff (i : ℕ) F :=
  rfl

theorem ker_truncCoeffs (M : ℕ) :
    LinearMap.ker (truncCoeffs g M) = (truncI g M).restrictScalars g := by
  ext F
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, mem_truncI_iff]
  constructor
  · intro h m hm
    exact congrFun h ⟨m, hm⟩
  · intro h
    funext i
    exact h i i.2

theorem truncCoeffs_surjective (M : ℕ) : Function.Surjective (truncCoeffs g M) := fun c =>
  ⟨PowerSeries.mk fun m => if h : m < M + 1 then c ⟨m, h⟩ else 0, by
    funext i
    rw [truncCoeffs_apply, PowerSeries.coeff_mk, dif_pos i.2]⟩

private def truncAux₁ (M : ℕ) :=
  LinearMap.quotKerEquivOfSurjective (truncCoeffs g M) (truncCoeffs_surjective g M)

private def truncAux₂ (M : ℕ) :=
  Submodule.quotEquivOfEq _ _ (ker_truncCoeffs g M).symm

private def truncAux₃ (M : ℕ) :=
  (Submodule.Quotient.restrictScalarsEquiv g (truncI g M)).symm

private def truncAux₂₁ (M : ℕ) := (truncAux₂ g M) ≪≫ₗ (truncAux₁ g M)

def truncEquiv (M : ℕ) : TruncPS g M ≃ₗ[g] (Fin (M + 1) → g) :=
  (truncAux₃ g M) ≪≫ₗ (truncAux₂₁ g M)

def thickPolyT (n M : ℕ) : Polynomial (TruncPS g M) :=
  (thickPoly g p n).map (Ideal.Quotient.mk (truncI g M))

theorem monic_thickPolyT {n : ℕ} (hn : n ≠ 0) (M : ℕ) : (thickPolyT g p n M).Monic :=
  (monic_thickPoly g p hn).map _

abbrev ThickT (n M : ℕ) : Type u := AdjoinRoot (thickPolyT g p n M)

def basisT {n : ℕ} (hn : n ≠ 0) (M : ℕ) :
    Module.Basis (Fin (M + 1) × Fin (AdjoinRoot.powerBasis' (monic_thickPolyT g p hn M)).dim) g
      (ThickT g p n M) :=
  (Module.Basis.ofEquivFun (truncEquiv g M)).smulTower (AdjoinRoot.powerBasis' (monic_thickPolyT g p hn M)).basis

theorem nzd_thickT {n : ℕ} (hn : n ≠ 0) (M : ℕ) (hg : (p : g) ∈ nonZeroDivisors g) :
    (p : ThickT g p n M) ∈ nonZeroDivisors (ThickT g p n M) :=
  mem_nonZeroDivisors_of_equiv p (A := g) (basisT g p hn M).equivFun hg

theorem isAdicComplete_thickT {n : ℕ} (hn : n ≠ 0) (M : ℕ) [IsAdicComplete (Ideal.span {(p : g)}) g] :
    IsAdicComplete (Ideal.span {(p : ThickT g p n M)}) (ThickT g p n M) :=
  isAdicComplete_of_equiv p (A := g) (basisT g p hn M).equivFun

theorem root_pow_T (n M : ℕ) : (AdjoinRoot.root (thickPolyT g p n M)) ^ n =
    (p : ThickT g p n M) *
      AdjoinRoot.of (thickPolyT g p n M) (Ideal.Quotient.mk (truncI g M) PowerSeries.X) := by
  have h : Polynomial.eval₂ (AdjoinRoot.of (thickPolyT g p n M)) (AdjoinRoot.root (thickPolyT g p n M))
      ((Polynomial.X ^ n - Polynomial.C ((p : PowerSeries g) * PowerSeries.X)).map
        (Ideal.Quotient.mk (truncI g M))) = 0 :=
    AdjoinRoot.eval₂_root _
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.eval₂_sub,
    Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero] at h
  simpa only [map_mul, map_natCast] using h

theorem isNilpotent_rootT (n M : ℕ) : IsNilpotent (AdjoinRoot.root (thickPolyT g p n M)) := by
  refine ⟨n * (M + 1), ?_⟩
  have hX : (Ideal.Quotient.mk (truncI g M) (PowerSeries.X ^ (M + 1) : PowerSeries g)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  rw [pow_mul, root_pow_T, mul_pow, ← map_pow, ← map_pow, hX, map_zero, mul_zero]

theorem eval₂_thickPoly_trunc_eq_zero (n M : ℕ) :
    Polynomial.eval₂ ((AdjoinRoot.of (thickPolyT g p n M)).comp (Ideal.Quotient.mk (truncI g M)))
      (AdjoinRoot.root (thickPolyT g p n M)) (thickPoly g p n) = 0 := by
  rw [← Polynomial.eval₂_map]
  exact AdjoinRoot.eval₂_root _

def thickTrunc (n M : ℕ) : Thick g p n →ₐ[𝓞] ThickT g p n M where
  toRingHom := AdjoinRoot.lift ((AdjoinRoot.of (thickPolyT g p n M)).comp (Ideal.Quotient.mk (truncI g M)))
      (AdjoinRoot.root (thickPolyT g p n M)) (eval₂_thickPoly_trunc_eq_zero g p n M)
  commutes' o := by
    show AdjoinRoot.lift _ (AdjoinRoot.root (thickPolyT g p n M)) _ (algebraMap 𝓞 (Thick g p n) o) =
      algebraMap 𝓞 (ThickT g p n M) o
    rw [IsScalarTower.algebraMap_apply 𝓞 (PowerSeries g) (Thick g p n), AdjoinRoot.algebraMap_eq,
      AdjoinRoot.lift_of, IsScalarTower.algebraMap_apply 𝓞 (TruncPS g M) (ThickT g p n M),
      AdjoinRoot.algebraMap_eq, IsScalarTower.algebraMap_apply 𝓞 (PowerSeries g) (TruncPS g M),
      Ideal.Quotient.algebraMap_eq]
    rfl

theorem thickTrunc_of (n M : ℕ) (F : PowerSeries g) :
    thickTrunc 𝓞 g p n M (AdjoinRoot.of _ F) = AdjoinRoot.of _ (Ideal.Quotient.mk (truncI g M) F) :=
  AdjoinRoot.lift_of (eval₂_thickPoly_trunc_eq_zero g p n M)

theorem thickTrunc_root (n M : ℕ) :
    thickTrunc 𝓞 g p n M (AdjoinRoot.root _) = AdjoinRoot.root _ :=
  AdjoinRoot.lift_root (eval₂_thickPoly_trunc_eq_zero g p n M)

theorem thickTrunc_mk (n M : ℕ) (q : Polynomial (PowerSeries g)) :
    thickTrunc 𝓞 g p n M (AdjoinRoot.mk _ q) = AdjoinRoot.mk _ (q.map (Ideal.Quotient.mk (truncI g M))) := by
  show AdjoinRoot.lift _ _ (eval₂_thickPoly_trunc_eq_zero g p n M) (AdjoinRoot.mk _ q) = _
  rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq, ← Polynomial.aeval_def,
    AdjoinRoot.aeval_eq]

theorem thickTrunc_algebraMap (n M : ℕ) (a : g) :
    thickTrunc 𝓞 g p n M (algebraMap g _ a) = algebraMap g _ a := by
  rw [IsScalarTower.algebraMap_apply g (PowerSeries g) (Thick g p n), AdjoinRoot.algebraMap_eq, thickTrunc_of,
    IsScalarTower.algebraMap_apply g (TruncPS g M) (ThickT g p n M), AdjoinRoot.algebraMap_eq,
    IsScalarTower.algebraMap_apply g (PowerSeries g) (TruncPS g M), Ideal.Quotient.algebraMap_eq]

theorem nontrivial_truncPS [Nontrivial g] (M : ℕ) : Nontrivial (TruncPS g M) :=
  (truncEquiv g M).symm.injective.nontrivial

theorem eq_of_forall_thickTrunc_eq {n : ℕ} (hn : n ≠ 0) {b c : Thick g p n}
    (h : ∀ M, thickTrunc 𝓞 g p n M b = thickTrunc 𝓞 g p n M c) : b = c := by
  rcases subsingleton_or_nontrivial g with hg | hg
  · haveI : Subsingleton (PowerSeries g) := (coeffEquiv g).injective.subsingleton
    have h01 : (0 : Thick g p n) = 1 := by
      rw [← map_one (AdjoinRoot.of (thickPoly g p n)), Subsingleton.elim (1 : PowerSeries g) 0, map_zero]
    haveI := subsingleton_of_zero_eq_one h01
    exact Subsingleton.elim _ _
  rw [← sub_eq_zero]
  set a := b - c with ha_def
  have ha : ∀ M, thickTrunc 𝓞 g p n M a = 0 := fun M => by rw [ha_def, map_sub, h M, sub_self]
  have hf := monic_thickPoly g p hn
  have hfdeg : (thickPoly g p n).natDegree = n := Polynomial.natDegree_X_pow_sub_C
  have hf1 : thickPoly g p n ≠ 1 := fun h1 => hn (by rw [← hfdeg, h1, Polynomial.natDegree_one])

  obtain ⟨q₀, hq₀⟩ := AdjoinRoot.mk_surjective a
  set q := q₀ %ₘ thickPoly g p n with hq_def
  have hqa : AdjoinRoot.mk (thickPoly g p n) q = a := by
    rw [← hq₀, AdjoinRoot.mk_eq_mk]
    exact ⟨-(q₀ /ₘ thickPoly g p n), by
      rw [mul_neg, eq_neg_iff_add_eq_zero, hq_def]
      have := Polynomial.modByMonic_add_div q₀ (thickPoly g p n)
      linear_combination this⟩
  have hqdeg : q.natDegree < n := hfdeg ▸ Polynomial.natDegree_modByMonic_lt q₀ hf hf1

  have hqM : ∀ M, q.map (Ideal.Quotient.mk (truncI g M)) = 0 := by
    intro M
    haveI := nontrivial_truncPS g M
    have hdvd : thickPolyT g p n M ∣ q.map (Ideal.Quotient.mk (truncI g M)) := by
      rw [← AdjoinRoot.mk_eq_zero, ← thickTrunc_mk 𝓞 g p n M q, hqa, ha M]
    by_contra hne
    refine (monic_thickPolyT g p hn M).not_dvd_of_natDegree_lt hne ?_ hdvd
    calc (q.map (Ideal.Quotient.mk (truncI g M))).natDegree ≤ q.natDegree := Polynomial.natDegree_map_le
      _ < n := hqdeg
      _ = (thickPolyT g p n M).natDegree := by
        rw [thickPolyT, hf.natDegree_map, hfdeg]

  have hq0 : q = 0 := by
    ext k m
    rw [Polynomial.coeff_zero, map_zero]
    have hk : Ideal.Quotient.mk (truncI g m) (q.coeff k) = 0 := by
      rw [← Polynomial.coeff_map, hqM m, Polynomial.coeff_zero]
    exact (mem_truncI_iff g).1 (Ideal.Quotient.eq_zero_iff_mem.1 hk) m (Nat.lt_succ_self m)
  rw [← hqa, hq0, map_zero]

end Step

section Induction

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {d : ℕ}
  (μ : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (Fin d → g) → (Fin d → g) → (Fin d → g))
  (Φ : MvFormalGroup d 𝓞)

section Count

open Classical

def nnCard {g : Type u} [CommRing g] (t : Fin d ⊕ Fin d → g) : ℕ :=
  (Finset.univ.filter fun s => ¬ IsNilpotent (t s)).card

theorem forall_isNilpotent_of_nnCard_eq_zero {g : Type u} [CommRing g] {t : Fin d ⊕ Fin d → g}
    (h : nnCard t = 0) : ∀ s, IsNilpotent (t s) := by
  intro s
  by_contra hs
  rw [nnCard, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  exact h (Finset.mem_univ s) hs

theorem exists_not_isNilpotent_of_nnCard_ne_zero {g : Type u} [CommRing g] {t : Fin d ⊕ Fin d → g}
    (h : nnCard t ≠ 0) : ∃ s, ¬ IsNilpotent (t s) := by
  by_contra hall
  push Not at hall
  apply h
  rw [nnCard, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun s _ hs => hs (hall s)

theorem nnCard_lt {g g' : Type u} [CommRing g] [CommRing g'] {t : Fin d ⊕ Fin d → g}
    {t' : Fin d ⊕ Fin d → g'} {j : Fin d ⊕ Fin d} (hj : ¬ IsNilpotent (t j)) (hj' : IsNilpotent (t' j))
    (himp : ∀ s, s ≠ j → IsNilpotent (t s) → IsNilpotent (t' s)) : nnCard t' < nnCard t := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j, by simp [hj], by simp [hj']⟩
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    intro hts
    by_cases hsj : s = j
    · exact hs (hsj ▸ hj')
    · exact hs (himp s hsj hts)

end Count

theorem good_of_nnCard_le (hnat : NatHyp p μ)
    (hbase : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
      IsAdicComplete (Ideal.span {(p : g)}) g → ∀ t : Fin d ⊕ Fin d → g, (∀ s, IsNilpotent (t s)) →
      Good p μ Φ g t) :
    ∀ (k : ℕ) (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
      IsAdicComplete (Ideal.span {(p : g)}) g → ∀ t : Fin d ⊕ Fin d → g,
      (∀ s, t s ∈ (Ideal.span {(p : g)}).radical) → nnCard t ≤ k → Good p μ Φ g t := by
  intro k
  induction k with
  | zero =>
    intro g _ _ hg hgc t _ hk
    exact hbase g hg hgc t (forall_isNilpotent_of_nnCard_eq_zero (Nat.le_zero.1 hk))
  | succ k ih =>
    intro g _ _ hg hgc t ht hk
    by_cases hle : nnCard t ≤ k
    · exact ih g hg hgc t ht hle
    obtain ⟨j, hj⟩ := exists_not_isNilpotent_of_nnCard_ne_zero (t := t) (by omega)

    obtain ⟨e, he⟩ := ht j
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 he
    set z : g := t j with hz_def
    have hn : 2 * (e + 1) ≠ 0 := by omega
    have hz : z ^ (2 * (e + 1)) = (p : g) * ((p : g) * (w * z) ^ 2) := by
      have h1 : z ^ (e + 1) = (p : g) * (w * z) := by rw [pow_succ, ← hw]; ring
      rw [pow_mul', h1]; ring
    have hv : (p : g) * (w * z) ^ 2 ∈ (Ideal.span {(p : g)}).radical :=
      Ideal.le_radical (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    haveI := hgc

    have hB := nzd_thick g p hn hg
    haveI hBc := isAdicComplete_thick g p hn
    let π : Thick g p (2 * (e + 1)) →ₐ[𝓞] g := thickEval 𝓞 p hv hz
    let t' : Fin d ⊕ Fin d → Thick g p (2 * (e + 1)) :=
      Function.update (fun s => algebraMap g _ (t s)) j (AdjoinRoot.root _)
    have ht'j : t' j = AdjoinRoot.root _ := Function.update_self _ _ _
    have ht's : ∀ s, s ≠ j → t' s = algebraMap g _ (t s) := fun s hs => Function.update_of_ne hs _ _
    have hπt' : ∀ s, π (t' s) = t s := by
      intro s
      by_cases hs : s = j
      · rw [hs, ht'j]
        exact thickEval_root 𝓞 p hv hz
      · rw [ht's s hs]
        exact thickEval_algebraMap 𝓞 p hv hz _
    have ht' : ∀ s, t' s ∈ (Ideal.span {(p : Thick g p (2 * (e + 1)))}).radical := by
      intro s
      by_cases hs : s = j
      · rw [hs, ht'j]
        exact root_mem_radical g p _
      · rw [ht's s hs]
        exact map_mem_radical p (algebraMap g (Thick g p (2 * (e + 1)))) (ht s)

    have hgoodB : Good p μ Φ (Thick g p (2 * (e + 1))) t' := by
      intro i
      apply eq_of_forall_thickTrunc_eq 𝓞 g p hn
      intro M
      haveI := isAdicComplete_thickT g p hn M
      have hT := nzd_thickT g p hn M hg
      have hcard : nnCard (thickTrunc 𝓞 g p (2 * (e + 1)) M ∘ t') ≤ k := by
        have hlt := nnCard_lt (t := t) (t' := thickTrunc 𝓞 g p (2 * (e + 1)) M ∘ t') hj
          (by rw [Function.comp_apply, ht'j, thickTrunc_root]; exact isNilpotent_rootT g p _ M)
          (fun s hs hts => by
            rw [Function.comp_apply, ht's s hs, thickTrunc_algebraMap]
            exact hts.map _)
        omega
      have ih' := ih (ThickT g p (2 * (e + 1)) M) hT inferInstance (thickTrunc 𝓞 g p (2 * (e + 1)) M ∘ t')
        (fun s => map_mem_radical p (thickTrunc 𝓞 g p (2 * (e + 1)) M) (ht' s)) hcard i
      have hn' := hnat (Thick g p (2 * (e + 1))) (ThickT g p (2 * (e + 1)) M) hB hBc hT inferInstance
        (thickTrunc 𝓞 g p (2 * (e + 1)) M) (t' ∘ Sum.inl) (t' ∘ Sum.inr) (fun j => ht' _) (fun j => ht' _)
      rw [show thickTrunc 𝓞 g p (2 * (e + 1)) M (μ _ (t' ∘ Sum.inl) (t' ∘ Sum.inr) i) =
          (thickTrunc 𝓞 g p (2 * (e + 1)) M ∘ μ _ (t' ∘ Sum.inl) (t' ∘ Sum.inr)) i from rfl, ← hn',
        map_adicEval (Ideal.span {(p : Thick g p (2 * (e + 1)))}) (Ideal.span {(p : ThickT g p (2 * (e + 1)) M)})
          (thickTrunc 𝓞 g p (2 * (e + 1)) M) (Submodule.fg_span_singleton _)
          (fun s hs => map_mem_radical_of_mem_span p _ hs) ht']
      exact ih'

    intro i
    have hn' := hnat (Thick g p (2 * (e + 1))) g hB hBc hg hgc π (t' ∘ Sum.inl) (t' ∘ Sum.inr)
      (fun j => ht' _) (fun j => ht' _)
    have h1 : π ∘ (t' ∘ Sum.inl) = t ∘ Sum.inl := funext fun j => hπt' _
    have h2 : π ∘ (t' ∘ Sum.inr) = t ∘ Sum.inr := funext fun j => hπt' _
    rw [h1, h2] at hn'
    rw [show μ g (t ∘ Sum.inl) (t ∘ Sum.inr) i = π (μ _ (t' ∘ Sum.inl) (t' ∘ Sum.inr) i) from congrFun hn' i,
      hgoodB i, map_adicEval _ (Ideal.span {(p : g)}) π (Submodule.fg_span_singleton _)
        (fun s hs => map_mem_radical_of_mem_span p π hs) ht']
    exact congrArg (fun w => adicEval (Ideal.span {(p : g)}) w (Φ.toPowerSeries i)) (funext hπt')

end Induction

theorem main {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (d : ℕ)
    (μ : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (Fin d → g) → (Fin d → g) → (Fin d → g))
    (hμ_mem : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
      IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (x y : Fin d → g),
      (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      ∀ j, μ g x y j ∈ (Ideal.span {(p : g)}).radical)
    (hμ_zero : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
      IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (x : Fin d → g),
      (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → μ g x 0 = x ∧ μ g 0 x = x)
    (hμ_assoc : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
      IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (x y z : Fin d → g),
      (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      (∀ j, z j ∈ (Ideal.span {(p : g)}).radical) → μ g (μ g x y) z = μ g x (μ g y z))
    (hμ_comm : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
      IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (x y : Fin d → g),
      (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) → μ g x y = μ g y x)
    (hμ_nat : ∀ (g g' : Type u) [CommRing g] [Algebra 𝓞 g] [CommRing g'] [Algebra 𝓞 g'],
      (p : g) ∈ nonZeroDivisors g → IsAdicComplete (Ideal.span {(p : g)}) g →
      (p : g') ∈ nonZeroDivisors g' → IsAdicComplete (Ideal.span {(p : g')}) g' →
      ∀ (φ : g →ₐ[𝓞] g') (x y : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      μ g' (φ ∘ x) (φ ∘ y) = φ ∘ μ g x y) :
    ∃! Φ : MvFormalGroup d 𝓞, Φ.IsComm ∧
      ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (x y : Fin d → g),
        (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
        ∀ i, μ g x y i =
          MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim x y) (Φ.toPowerSeries i) := by

  obtain ⟨Φ, ⟨hΦc, hΦ⟩, huniq⟩ :=
    MvFormalGroup.existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural p hp d μ
      (fun g _ _ _ _ x y hx hy => hμ_mem g (nzd_of_free p hp g) (isAdicComplete_of_free 𝓞 p g) x y hx hy)
      (fun g _ _ _ _ x hx => hμ_zero g (nzd_of_free p hp g) (isAdicComplete_of_free 𝓞 p g) x hx)
      (fun g _ _ _ _ x y z hx hy hz => hμ_assoc g (nzd_of_free p hp g) (isAdicComplete_of_free 𝓞 p g) x y z hx hy hz)
      (fun g _ _ _ _ x y hx hy => hμ_comm g (nzd_of_free p hp g) (isAdicComplete_of_free 𝓞 p g) x y hx hy)
      (fun g g' _ _ _ _ _ _ _ _ φ x y hx hy => hμ_nat g g' (nzd_of_free p hp g) (isAdicComplete_of_free 𝓞 p g)
        (nzd_of_free p hp g') (isAdicComplete_of_free 𝓞 p g') φ x y hx hy)
  refine ⟨Φ, ⟨hΦc, fun g _ _ hg hgc x y hx hy i => ?_⟩, ?_⟩
  · have hrad : ∀ s, Sum.elim x y s ∈ (Ideal.span {(p : g)}).radical := by
      rintro (j | j)
      exacts [hx j, hy j]
    exact good_of_nnCard_le p μ Φ hμ_nat (good_of_isNilpotent p μ hp hμ_nat Φ hΦ) (nnCard (Sum.elim x y)) g hg hgc
      (Sum.elim x y) hrad le_rfl i
  · rintro Ψ ⟨hΨc, hΨ⟩
    exact huniq Ψ ⟨hΨc, fun g _ _ _ _ x y hx hy i => hΨ g (nzd_of_free p hp g) (isAdicComplete_of_free 𝓞 p g) x y
      (fun j => mem_radical_of_isNilpotent' (hx j) _) (fun j => mem_radical_of_isNilpotent' (hy j) _) i⟩

end MvFormalGroup.RadicalLaw
p2m_reactivate "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural_of_mem_radical.MvFormalGroup P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural_of_mem_radical.MvFormalGroup.RadicalLaw"
p2m_reactivate "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural_of_mem_radical.MvFormalGroup"

end
p2m_reactivate "P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural_of_mem_radical.MvFormalGroup P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural_of_mem_radical.MvFormalGroup.RadicalLaw"

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞] (d : ℕ)
    (μ : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (Fin d → g) → (Fin d → g) → (Fin d → g))
    (hμ_mem : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
      IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (x y : Fin d → g),
      (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      ∀ j, μ g x y j ∈ (Ideal.span {(p : g)}).radical)
    (hμ_zero : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
      IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (x : Fin d → g),
      (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → μ g x 0 = x ∧ μ g 0 x = x)
    (hμ_assoc : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
      IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (x y z : Fin d → g),
      (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      (∀ j, z j ∈ (Ideal.span {(p : g)}).radical) → μ g (μ g x y) z = μ g x (μ g y z))
    (hμ_comm : ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
      IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (x y : Fin d → g),
      (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) → μ g x y = μ g y x)
    (hμ_nat : ∀ (g g' : Type u) [CommRing g] [Algebra 𝓞 g] [CommRing g'] [Algebra 𝓞 g'],
      (p : g) ∈ nonZeroDivisors g → IsAdicComplete (Ideal.span {(p : g)}) g →
      (p : g') ∈ nonZeroDivisors g' → IsAdicComplete (Ideal.span {(p : g')}) g' →
      ∀ (φ : g →ₐ[𝓞] g') (x y : Fin d → g), (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
      μ g' (φ ∘ x) (φ ∘ y) = φ ∘ μ g x y) :
    ∃! Φ : MvFormalGroup d 𝓞, Φ.IsComm ∧
      ∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (x y : Fin d → g),
        (∀ j, x j ∈ (Ideal.span {(p : g)}).radical) → (∀ j, y j ∈ (Ideal.span {(p : g)}).radical) →
        ∀ i, μ g x y i =
          MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim x y) (Φ.toPowerSeries i) :=
  MvFormalGroup.RadicalLaw.main p hp d μ hμ_mem hμ_zero hμ_assoc hμ_comm hμ_nat

end S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural_of_mem_radical
end P2MW
export P2MW.S_MvFormalGroup_existsUnique_isComm_and_apply_eq_adicEval_toPowerSeries_of_natural_of_mem_radical (solution)
