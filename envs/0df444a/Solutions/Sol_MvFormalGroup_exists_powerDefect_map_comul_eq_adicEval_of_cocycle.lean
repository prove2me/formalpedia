-- Prove2me | solution 1 for MvFormalGroup.exists_powerDefect_map_comul_eq_adicEval_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/935fae09-f985-5d48-ac32-3e26dd45b6ea

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_IsAdicComplete_of_module_finite_free_span_natCast
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_powerDefect_map_comul_eq_adicEval_of_cocycle

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

open scoped TensorProduct
open MvPowerSeries

universe u v

namespace MvFormalGroup
p2m_export "MvFormalGroup" "IsComm map nthSeries mk toPowerSeries constantCoeff_eq_zero adicEval map_adicEval Points Points.val_add Points.val_nsmul Points.map Points.ext"
namespace PowerDefect
p2m_open "MvFormalGroup"

section Abstract

variable {M : Type*} [CommMonoid M] {A : Type*} [AddCommGroup A]

def defect (c : M → M → A) : ℕ → M → A
  | 0, _ => 0
  | n + 1, f => defect c n f + c (f ^ n) f

variable (c : M → M → A)

theorem defect_zero (f : M) : defect c 0 f = 0 := rfl

theorem defect_succ (n : ℕ) (f : M) : defect c (n + 1) f = defect c n f + c (f ^ n) f := rfl

structure IsCocycle (c : M → M → A) : Prop where
  symm : ∀ a b, c a b = c b a
  coc : ∀ a b e, c a b + c (a * b) e = c b e + c a (b * e)
  one_left : ∀ a, c 1 a = 0

variable {c}

theorem IsCocycle.one_right (hc : IsCocycle c) (a : M) : c a 1 = 0 := by
  rw [hc.symm, hc.one_left]

theorem defect_one (h1 : ∀ a, c 1 a = 0) (n : ℕ) : defect c n 1 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [defect_succ, ih, one_pow, h1, add_zero]

theorem defect_add (hc : IsCocycle c) (f : M) (a b : ℕ) :
    defect c (a + b) f = defect c a f + defect c b f + c (f ^ a) (f ^ b) := by
  induction b with
  | zero => rw [add_zero, defect_zero, add_zero, pow_zero, hc.one_right, add_zero]
  | succ b ih =>
    have key := hc.coc (f ^ a) (f ^ b) f
    rw [← add_assoc, defect_succ, ih, defect_succ, pow_add, pow_succ]
    calc defect c a f + defect c b f + c (f ^ a) (f ^ b) + c (f ^ a * f ^ b) f
        = defect c a f + defect c b f + (c (f ^ a) (f ^ b) + c (f ^ a * f ^ b) f) := by abel
      _ = defect c a f + defect c b f + (c (f ^ b) f + c (f ^ a) (f ^ b * f)) := by rw [key]
      _ = defect c a f + (defect c b f + c (f ^ b) f) + c (f ^ a) (f ^ b * f) := by abel

theorem defect_mul_of_pow_eq_one (hc : IsCocycle c) (f : M) (q : ℕ) (hq : f ^ q = 1) (m : ℕ) :
    defect c (q * m) f = m • defect c q f := by
  induction m with
  | zero => rw [mul_zero, defect_zero, zero_nsmul]
  | succ m ih =>
    rw [mul_add, mul_one, defect_add hc, ih, pow_mul, hq, one_pow, hc.one_left, add_zero, succ_nsmul]

theorem defect_mul_add_nsmul (hc : IsCocycle c) (f h : M) (n : ℕ) :
    defect c n (f * h) + n • c f h = defect c n f + (defect c n h + c (f ^ n) (h ^ n)) := by
  induction n with
  | zero => rw [defect_zero, defect_zero, defect_zero, zero_nsmul, pow_zero, pow_zero, hc.one_left, add_zero, add_zero]
  | succ n ih =>
    have k1 := hc.coc (f ^ n) (h ^ n) (f * h)
    have k2 := hc.coc (h ^ n) f h
    have k3 := hc.coc (f ^ n) f (h ^ n * h)
    have k4 := hc.coc f (h ^ n) h
    have s1 : c (h ^ n) f = c f (h ^ n) := hc.symm _ _
    have e1 : h ^ n * (f * h) = f * (h ^ n * h) := mul_left_comm _ _ _
    have e2 : h ^ n * f = f * h ^ n := mul_comm _ _
    rw [defect_succ, defect_succ, defect_succ, succ_nsmul, mul_pow, pow_succ, pow_succ]
    calc defect c n (f * h) + c (f ^ n * h ^ n) (f * h) + (n • c f h + c f h)
        = (defect c n (f * h) + n • c f h) + (c (f ^ n * h ^ n) (f * h) + c f h) := by abel
      _ = defect c n f + (defect c n h + c (f ^ n) (h ^ n)) + (c (f ^ n * h ^ n) (f * h) + c f h) := by rw [ih]
      _ = defect c n f + defect c n h + (c (f ^ n) (h ^ n) + c (f ^ n * h ^ n) (f * h)) + c f h := by abel
      _ = defect c n f + defect c n h + (c (h ^ n) (f * h) + c (f ^ n) (h ^ n * (f * h))) + c f h := by rw [k1]
      _ = defect c n f + defect c n h + c (f ^ n) (h ^ n * (f * h)) + (c f h + c (h ^ n) (f * h)) := by abel
      _ = defect c n f + defect c n h + c (f ^ n) (h ^ n * (f * h)) + (c (h ^ n) f + c (h ^ n * f) h) := by rw [← k2]
      _ = defect c n f + defect c n h + c (f ^ n) (f * (h ^ n * h)) + (c f (h ^ n) + c (f * h ^ n) h) := by
          rw [e1, s1, e2]
      _ = defect c n f + defect c n h + c (f ^ n) (f * (h ^ n * h)) + (c (h ^ n) h + c f (h ^ n * h)) := by rw [k4]
      _ = defect c n f + defect c n h + c (h ^ n) h + (c f (h ^ n * h) + c (f ^ n) (f * (h ^ n * h))) := by abel
      _ = defect c n f + defect c n h + c (h ^ n) h + (c (f ^ n) f + c (f ^ n * f) (h ^ n * h)) := by rw [← k3]
      _ = defect c n f + c (f ^ n) f + (defect c n h + c (h ^ n) h + c (f ^ n * f) (h ^ n * h)) := by abel

end Abstract

section Helpers

theorem map_mem_span_natCast {A B : Type*} [Semiring A] [Semiring B] {F : Type*} [FunLike F A B]
    [RingHomClass F A B] (φ : F) (p : ℕ) {x : A} (hx : x ∈ Ideal.span {(p : A)}) : φ x ∈ Ideal.span {(p : B)} := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [map_mul, map_natCast]
  exact Ideal.mem_span_singleton'.mpr ⟨φ y, rfl⟩

theorem fg_span_natCast (A : Type*) [CommRing A] (p : ℕ) : (Ideal.span {(p : A)}).FG :=
  ⟨{(p : A)}, by rw [Finset.coe_singleton]⟩

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {σ : Type*}

theorem mvPolynomial_eval₂_eq_sum_of_forall_prod_eq_zero (x : σ → S) (T : Finset (σ →₀ ℕ))
    (hT : ∀ m, m ∉ T → m.prod (fun s e => x s ^ e) = 0) (r : MvPolynomial σ R) :
    MvPolynomial.eval₂ (algebraMap R S) x r =
      ∑ m ∈ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) := by
  classical
  rw [MvPolynomial.eval₂_eq]
  change ∑ m ∈ r.support, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) = _
  have h1 : ∑ m ∈ r.support, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) =
      ∑ m ∈ r.support ∪ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) :=
    Finset.sum_subset Finset.subset_union_left fun m _ hm => by
      rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]
  have h2 : ∑ m ∈ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) =
      ∑ m ∈ r.support ∪ T, algebraMap R S (MvPolynomial.coeff m r) * m.prod (fun s e => x s ^ e) :=
    Finset.sum_subset Finset.subset_union_right fun m _ hm => by
      rw [hT m hm, mul_zero]
  rw [h1, h2]

open MvPowerSeries.WithPiTopology in

theorem adicEval_eq_aeval_of_forall_prod_eq_zero
    (J : Ideal S) (hJ : IsHausdorff J S) (x : σ → S) (F : MvPowerSeries σ R)
    (q : MvPolynomial σ R) (T : Finset (σ →₀ ℕ))
    (hT : ∀ m, m ∉ T → m.prod (fun s e => x s ^ e) = 0)
    (hq : ∀ m ∈ T, MvPolynomial.coeff m q = MvPowerSeries.coeff m F) :
    adicEval J x F = MvPolynomial.aeval x q := by
  classical
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  haveI : T2Space S := (IsAdic.isHausdorff_iff (show IsAdic J from rfl)).mp hJ
  set c : S := ∑ m ∈ T, algebraMap R S (MvPowerSeries.coeff m F) * m.prod (fun s e => x s ^ e)
    with hc
  have key : ∀ r : MvPolynomial σ R,
      (∀ m ∈ T, MvPolynomial.coeff m r = MvPowerSeries.coeff m F) →
      MvPolynomial.eval₂ (algebraMap R S) x r = c := fun r hr => by
    rw [mvPolynomial_eval₂_eq_sum_of_forall_prod_eq_zero x T hT r, hc]
    exact Finset.sum_congr rfl fun m hm => by rw [hr m hm]
  rw [MvPolynomial.aeval_def, key q hq]
  change MvPowerSeries.eval₂ (algebraMap R S) x F = c
  unfold MvPowerSeries.eval₂
  split_ifs with H
  · refine key _ fun m _ => ?_
    rw [← MvPolynomial.coeff_coe, H.choose_spec]
  · refine MvPolynomial.toMvPowerSeries_isDenseInducing.extend_eq_of_tendsto ?_
    have hU : {G : MvPowerSeries σ R | ∀ m ∈ T, MvPowerSeries.coeff m G = MvPowerSeries.coeff m F} ∈
        nhds F := by
      have : {G : MvPowerSeries σ R | ∀ m ∈ T, MvPowerSeries.coeff m G = MvPowerSeries.coeff m F} =
          ⋂ m ∈ T, {G : MvPowerSeries σ R | MvPowerSeries.coeff m G = MvPowerSeries.coeff m F} := by
        ext G
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [this, Filter.biInter_finset_mem]
      intro m _
      exact ((isOpen_discrete ({MvPowerSeries.coeff m F} : Set R)).preimage
        (MvPowerSeries.WithPiTopology.continuous_coeff (R := R) m)).mem_nhds rfl
    refine Filter.Tendsto.congr' (Filter.mem_of_superset (Filter.preimage_mem_comap hU)
      fun r hr => ?_) tendsto_const_nhds
    exact (key r fun m hm => by rw [← MvPolynomial.coeff_coe]; exact hr m hm).symm

theorem adicEval_zero_of_constantCoeff_eq_zero (J : Ideal S) (hJ : IsHausdorff J S) {F : MvPowerSeries σ R}
    (hF : F.constantCoeff = 0) : adicEval J (fun _ : σ => (0 : S)) F = 0 := by
  classical
  rw [adicEval_eq_aeval_of_forall_prod_eq_zero J hJ (fun _ => (0 : S)) F (0 : MvPolynomial σ R) {0} ?_ ?_, map_zero]
  · intro m hm
    rw [Finset.mem_singleton] at hm
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hm
    exact Finset.prod_eq_zero hs (zero_pow (Finsupp.mem_support_iff.mp hs))
  · intro m hm
    rw [Finset.mem_singleton] at hm
    subst hm
    rw [MvPolynomial.coeff_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hF]

theorem adicEval_mem_of_forall_mem [Finite σ] (J : Ideal S) [IsAdicComplete J S] (hJ : J.FG) {x : σ → S}
    (hx : ∀ s, x s ∈ J) {F : MvPowerSeries σ R} (hF : F.constantCoeff = 0) : adicEval J x F ∈ J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hφ : ∀ s ∈ J, Ideal.Quotient.mkₐ R J s ∈ (⊥ : Ideal (S ⧸ J)).radical := fun s hs => by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hs]
    exact Ideal.zero_mem _
  have key := map_adicEval (R := R) (S := S) (S' := S ⧸ J) J (⊥ : Ideal (S ⧸ J)) (Ideal.Quotient.mkₐ R J) hJ hφ
    (fun s => Ideal.le_radical (hx s)) F
  have hzero : (fun s => Ideal.Quotient.mkₐ R J (x s)) = fun _ => (0 : S ⧸ J) :=
    funext fun s => by rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr (hx s)]
  rw [hzero, adicEval_zero_of_constantCoeff_eq_zero ⊥ inferInstance hF] at key
  rw [← Ideal.Quotient.mkₐ_eq_mk R]
  exact key

end Helpers

section Lift

variable {𝓞 : Type*} [CommRing 𝓞] {E E' g g' : Type*} [CommRing E] [CommRing E'] [CommRing g] [CommRing g']
  [Algebra 𝓞 E] [Algebra 𝓞 E'] [Algebra 𝓞 g] [Algebra 𝓞 g']

theorem map_lift_apply (φ : g →ₐ[𝓞] g') (f h : E →ₐ[𝓞] g) (x : E ⊗[𝓞] E) :
    φ (Algebra.TensorProduct.lift f h (fun _ _ => Commute.all _ _) x) =
      Algebra.TensorProduct.lift (φ.comp f) (φ.comp h) (fun _ _ => Commute.all _ _) x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a b => rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_mul]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem lift_map_apply (f h : E →ₐ[𝓞] g) (a b : E' →ₐ[𝓞] E) (x : E' ⊗[𝓞] E') :
    Algebra.TensorProduct.lift f h (fun _ _ => Commute.all _ _) (Algebra.TensorProduct.map a b x) =
      Algebra.TensorProduct.lift (f.comp a) (h.comp b) (fun _ _ => Commute.all _ _) x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a' b' => rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem lift_includeLeft_comp_includeRight_comp_apply (a b : E →ₐ[𝓞] E) (x : E ⊗[𝓞] E) :
    Algebra.TensorProduct.lift ((Algebra.TensorProduct.includeLeft : E →ₐ[𝓞] E ⊗[𝓞] E).comp a)
      ((Algebra.TensorProduct.includeRight : E →ₐ[𝓞] E ⊗[𝓞] E).comp b) (fun _ _ => Commute.all _ _) x =
      Algebra.TensorProduct.map a b x := by
  rw [← lift_map_apply, Algebra.TensorProduct.lift_includeLeft_includeRight, AlgHom.id_apply]

end Lift

section Conv

variable {𝓞 : Type*} [CommRing 𝓞] {E g : Type*} [CommRing E] [Bialgebra 𝓞 E] [CommRing g] [Algebra 𝓞 g]

theorem ofConv_mul (f h : WithConv (E →ₐ[𝓞] g)) :
    (f * h).ofConv = (Algebra.TensorProduct.lift f.ofConv h.ofConv (fun _ _ => Commute.all _ _)).comp
      (Bialgebra.comulAlgHom 𝓞 E) := by
  ext x
  rw [AlgHom.comp_apply]
  exact AlgHom.convMul_apply _ _ _

theorem ofConv_one : (1 : WithConv (E →ₐ[𝓞] g)).ofConv = (Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 E) := rfl

variable {g' : Type*} [CommRing g'] [Algebra 𝓞 g']

theorem toConv_comp_pow (φ : g →ₐ[𝓞] g') (f : WithConv (E →ₐ[𝓞] g)) (n : ℕ) :
    WithConv.toConv (φ.comp (f ^ n).ofConv) = (WithConv.toConv (φ.comp f.ofConv)) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    apply WithConv.ofConv_injective
    refine AlgHom.ext fun x => ?_
    change φ ((1 : WithConv (E →ₐ[𝓞] g)).ofConv x) = (1 : WithConv (E →ₐ[𝓞] g')).ofConv x
    rw [AlgHom.convOne_apply, AlgHom.convOne_apply, AlgHom.commutes]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    apply WithConv.ofConv_injective
    change φ.comp (f ^ n * f).ofConv = _
    rw [AlgHom.comp_convMul_distrib]

end Conv

section Realise

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm]
variable (E : Type u) [CommRing E] [Bialgebra 𝓞 E] [Coalgebra.IsCocomm 𝓞 E] (c₂ : Fin d → E ⊗[𝓞] E)
  (hc₂ : ∀ j, c₂ j ∈ Ideal.span {(p : E ⊗[𝓞] E)})
variable (g : Type u) [CommRing g] [Algebra 𝓞 g] [IsAdicComplete (Ideal.span {(p : g)}) g]

noncomputable def cpt (f h : WithConv (E →ₐ[𝓞] g)) : Points Φ g (Ideal.span {(p : g)}) where
  val j := Algebra.TensorProduct.lift f.ofConv h.ofConv (fun _ _ => Commute.all _ _) (c₂ j)
  mem_radical j := Ideal.le_radical
    (map_mem_span_natCast (Algebra.TensorProduct.lift f.ofConv h.ofConv (fun _ _ => Commute.all _ _)) p (hc₂ j))

omit [Φ.IsComm] [Coalgebra.IsCocomm 𝓞 E] [IsAdicComplete (Ideal.span {(p : g)}) g] in
theorem cpt_val (f h : WithConv (E →ₐ[𝓞] g)) (j : Fin d) :
    (cpt p Φ E c₂ hc₂ g f h).val j = Algebra.TensorProduct.lift f.ofConv h.ofConv (fun _ _ => Commute.all _ _) (c₂ j) :=
  rfl

omit [Φ.IsComm] [Coalgebra.IsCocomm 𝓞 E] [IsAdicComplete (Ideal.span {(p : g)}) g] in
theorem cpt_val_mem (f h : WithConv (E →ₐ[𝓞] g)) (j : Fin d) :
    (cpt p Φ E c₂ hc₂ g f h).val j ∈ Ideal.span {(p : g)} :=
  map_mem_span_natCast _ p (hc₂ j)

theorem dft_val_mem (n : ℕ) (f : WithConv (E →ₐ[𝓞] g)) (i : Fin d) :
    (defect (cpt p Φ E c₂ hc₂ g) n f).val i ∈ Ideal.span {(p : g)} := by
  induction n generalizing i with
  | zero => exact Ideal.zero_mem _
  | succ n ih =>
    rw [defect_succ, Points.val_add]
    refine adicEval_mem_of_forall_mem _ (fg_span_natCast g p) ?_ (Φ.constantCoeff_eq_zero i)
    rintro (j | j)
    · exact ih j
    · exact cpt_val_mem p Φ E c₂ hc₂ g _ _ j

theorem isCocycle
    (hunit : ∀ (f : E →ₐ[𝓞] g) (j : Fin d),
      Algebra.TensorProduct.lift ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 E)) f
        (fun _ _ => Commute.all _ _) (c₂ j) = 0)
    (hsymm : ∀ (f f' : E →ₐ[𝓞] g) (j : Fin d),
      Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ j) =
        Algebra.TensorProduct.lift f' f (fun _ _ => Commute.all _ _) (c₂ j))
    (hcoc : ∀ (f f' f'' : E →ₐ[𝓞] g),
      (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ j))) ((fun j => Algebra.TensorProduct.lift ((Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 E)) f'' (fun _ _ => Commute.all _ _) (c₂ j)))) (Φ.toPowerSeries i)) =
      (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _) (c₂ j))) ((fun j => Algebra.TensorProduct.lift f ((Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 E)) (fun _ _ => Commute.all _ _) (c₂ j)))) (Φ.toPowerSeries i))) :
    IsCocycle (cpt p Φ E c₂ hc₂ g) where
  symm a b := Points.ext (funext fun j => hsymm a.ofConv b.ofConv j)
  one_left a := Points.ext (funext fun j => by rw [cpt_val, ofConv_one, hunit]; rfl)
  coc a b e := by
    apply Points.ext
    funext i
    rw [Points.val_add, Points.val_add]
    show adicEval _ (Sum.elim (fun j => Algebra.TensorProduct.lift a.ofConv b.ofConv _ (c₂ j))
        (fun j => Algebra.TensorProduct.lift (a * b).ofConv e.ofConv _ (c₂ j))) _ =
      adicEval _ (Sum.elim (fun j => Algebra.TensorProduct.lift b.ofConv e.ofConv _ (c₂ j))
        (fun j => Algebra.TensorProduct.lift a.ofConv (b * e).ofConv _ (c₂ j))) _
    simp only [ofConv_mul]
    exact congrFun (hcoc a.ofConv b.ofConv e.ofConv) i

variable {g}
variable {g' : Type u} [CommRing g'] [Algebra 𝓞 g'] [IsAdicComplete (Ideal.span {(p : g')}) g']

omit [IsAdicComplete (Ideal.span {(p : g)}) g] [IsAdicComplete (Ideal.span {(p : g')}) g'] in
theorem mapsTo_radical (φ : g →ₐ[𝓞] g') : ∀ s ∈ Ideal.span {(p : g)}, φ s ∈ (Ideal.span {(p : g')}).radical :=
  fun _ hs => Ideal.le_radical (map_mem_span_natCast φ p hs)

omit [Φ.IsComm] [Coalgebra.IsCocomm 𝓞 E] in

theorem map_cpt (φ : g →ₐ[𝓞] g') (f h : WithConv (E →ₐ[𝓞] g)) :
    Points.map φ (fg_span_natCast g p) (mapsTo_radical p φ) (cpt p Φ E c₂ hc₂ g f h) =
      cpt p Φ E c₂ hc₂ g' (WithConv.toConv (φ.comp f.ofConv)) (WithConv.toConv (φ.comp h.ofConv)) :=
  Points.ext (funext fun j => map_lift_apply φ f.ofConv h.ofConv (c₂ j))

theorem map_dft (φ : g →ₐ[𝓞] g') (n : ℕ) (f : WithConv (E →ₐ[𝓞] g)) :
    Points.map φ (fg_span_natCast g p) (mapsTo_radical p φ) (defect (cpt p Φ E c₂ hc₂ g) n f) =
      defect (cpt p Φ E c₂ hc₂ g') n (WithConv.toConv (φ.comp f.ofConv)) := by
  induction n with
  | zero => rw [defect_zero, defect_zero, map_zero]
  | succ n ih =>
    rw [defect_succ, defect_succ, map_add, ih, map_cpt, toConv_comp_pow]

variable {E}
variable {E' : Type u} [CommRing E'] [Bialgebra 𝓞 E'] [Coalgebra.IsCocomm 𝓞 E'] (c₂' : Fin d → E' ⊗[𝓞] E')
  (hc₂' : ∀ j, c₂' j ∈ Ideal.span {(p : E' ⊗[𝓞] E')})

omit [Φ.IsComm] [Coalgebra.IsCocomm 𝓞 E] [IsAdicComplete (Ideal.span {(p : g)}) g] [Coalgebra.IsCocomm 𝓞 E'] in

theorem cpt_comp (st : E' →ₐc[𝓞] E)
    (hst : ∀ j, Algebra.TensorProduct.map (st : E' →ₐ[𝓞] E) (st : E' →ₐ[𝓞] E) (c₂' j) = c₂ j)
    (f h : WithConv (E →ₐ[𝓞] g)) :
    cpt p Φ E' c₂' hc₂' g (WithConv.toConv (f.ofConv.comp (st : E' →ₐ[𝓞] E)))
      (WithConv.toConv (h.ofConv.comp (st : E' →ₐ[𝓞] E))) = cpt p Φ E c₂ hc₂ g f h :=
  Points.ext (funext fun j => by rw [cpt_val, cpt_val, ← hst j, lift_map_apply])

theorem dft_comp (st : E' →ₐc[𝓞] E)
    (hst : ∀ j, Algebra.TensorProduct.map (st : E' →ₐ[𝓞] E) (st : E' →ₐ[𝓞] E) (c₂' j) = c₂ j)
    (n : ℕ) (f : WithConv (E →ₐ[𝓞] g)) :
    defect (cpt p Φ E' c₂' hc₂' g) n (WithConv.toConv (f.ofConv.comp (st : E' →ₐ[𝓞] E))) = defect (cpt p Φ E c₂ hc₂ g) n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h' : WithConv.toConv ((f ^ n).ofConv.comp (st : E' →ₐ[𝓞] E)) =
        (WithConv.toConv (f.ofConv.comp (st : E' →ₐ[𝓞] E))) ^ n :=
      congrArg WithConv.toConv (PDivisibleGroup.Hopf.convPow_comp_bialgHom f st n)
    rw [defect_succ, defect_succ, ih, ← cpt_comp p Φ c₂ hc₂ c₂' hc₂' st hst (f ^ n) f, h']

end Realise

section Kill

variable {𝓞 : Type*} [CommRing 𝓞] {E E' : Type*} [CommRing E] [CommRing E'] [Bialgebra 𝓞 E] [Bialgebra 𝓞 E']

theorem toConv_id_pow_eq_one (st : E' →ₐc[𝓞] E) (hst : Function.Surjective st) (N : ℕ)
    (hker : RingHom.ker st = PDivisibleGroup.Hopf.torsionIdeal 𝓞 E' N) :
    (WithConv.toConv (AlgHom.id 𝓞 E)) ^ N = 1 := by
  apply WithConv.ofConv_injective
  refine AlgHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := hst x
  change PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 E N (st y) = (1 : WithConv (E →ₐ[𝓞] E)).ofConv (st y)
  have hmem : PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 E' N y - algebraMap 𝓞 E' (Coalgebra.counit (R := 𝓞) y) ∈
      RingHom.ker st := by
    rw [hker]
    have h := PDivisibleGroup.Hopf.nsmulAlgHom_mem_torsionIdeal 𝓞 E'
      (PDivisibleGroup.Hopf.sub_algebraMap_counit_mem_augIdeal 𝓞 E' y) N
    rwa [map_sub, PDivisibleGroup.Hopf.nsmulAlgHom_algebraMap] at h
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
  rw [AlgHom.convOne_apply, PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply, hmem, CoalgHomClass.counit_comp_apply]
  exact (st : E' →ₐ[𝓞] E).commutes _

theorem natCast_mem_nonZeroDivisors {p : ℕ} (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (R : Type*) [CommRing R]
    [Algebra 𝓞 R] [Module.Free 𝓞 R] : (p : R) ∈ nonZeroDivisors R := by
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  set b := Module.Free.chooseBasis 𝓞 R
  have hpx : (p : 𝓞) • x = 0 := by
    rw [Algebra.smul_def, map_natCast, mul_comm]
    exact hx
  have hrepr : b.repr x = 0 := by
    ext i
    have hi := congrArg (fun y => b.repr y i) hpx
    simp only [map_smul, map_zero, Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul] at hi
    exact (mem_nonZeroDivisors_iff_right.1 hp) _ (by rw [mul_comm]; exact hi)
  exact b.repr.map_eq_zero_iff.1 hrepr

end Kill

end MvFormalGroup.PowerDefect

open _root_.MvFormalGroup _root_.P2MW.S_MvFormalGroup_exists_powerDefect_map_comul_eq_adicEval_of_cocycle.MvFormalGroup MvFormalGroup.PowerDefect in

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [(Ideal.span {(p : 𝓞)}).IsMaximal] [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (Φ : MvFormalGroup d 𝓞) [Φ.IsComm]

    (E : ℕ → Type u) [∀ v, CommRing (E v)] [∀ v, HopfAlgebra 𝓞 (E v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (E v)] [∀ v, Module.Free 𝓞 (E v)] [∀ v, Module.Finite 𝓞 (E v)]
    (st : ∀ v, E (v + 1) →ₐc[𝓞] E v) (hst : ∀ v, Function.Surjective (st v))
    (hkerE : ∀ v, RingHom.ker (st v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (E (v + 1)) (p ^ v))

    (c₂ : ∀ v, Fin d → E v ⊗[𝓞] E v)
    (hCOC :
      (∀ v i, Algebra.TensorProduct.map (st v : E (v + 1) →ₐ[𝓞] E v)
          (st v : E (v + 1) →ₐ[𝓞] E v) (c₂ (v + 1) i) = c₂ v i) ∧
      (∀ v i, c₂ v i ∈ Ideal.span {(p : E v ⊗[𝓞] E v)}) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f : E v →ₐ[𝓞] g) (j : Fin d),
          Algebra.TensorProduct.lift f ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 (E v))) (fun _ _ => Commute.all _ _) (c₂ v j) = 0 ∧
          Algebra.TensorProduct.lift ((Algebra.ofId 𝓞 g).comp (Bialgebra.counitAlgHom 𝓞 (E v))) f (fun _ _ => Commute.all _ _) (c₂ v j) = 0) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' : E v →ₐ[𝓞] g) (j : Fin d),
          Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j) = Algebra.TensorProduct.lift f' f (fun _ _ => Commute.all _ _) (c₂ v j)) ∧
      (∀ (g : Type u) [CommRing g] [Algebra 𝓞 g], (p : g) ∈ nonZeroDivisors g →
        IsAdicComplete (Ideal.span {(p : g)}) g → ∀ (v : ℕ) (f f' f'' : E v →ₐ[𝓞] g),
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _) (c₂ v j))) ((fun j => Algebra.TensorProduct.lift ((Algebra.TensorProduct.lift f f' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (E v))) f'' (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i)) =
          (fun i => MvFormalGroup.adicEval (Ideal.span {(p : g)}) (Sum.elim ((fun j => Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _) (c₂ v j))) ((fun j => Algebra.TensorProduct.lift f ((Algebra.TensorProduct.lift f' f'' (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom 𝓞 (E v))) (fun _ _ => Commute.all _ _) (c₂ v j)))) (Φ.toPowerSeries i)))) :
    ∃ C : ∀ v, ℕ → Fin d → E v,

      (∀ v i, C v 0 i = 0) ∧
      (∀ v n i, C v (n + 1) i =
        MvFormalGroup.adicEval (Ideal.span {(p : E v)})
          (Sum.elim (C v n) (fun j => Algebra.TensorProduct.lmul' 𝓞 (S := E v)
            (Algebra.TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (E v) n) (AlgHom.id 𝓞 (E v))
              (c₂ v j))))
          (Φ.toPowerSeries i)) ∧

      (∀ v n i, C v n i ∈ Ideal.span {(p : E v)}) ∧
      (∀ v n i, Coalgebra.counit (R := 𝓞) (C v n i) = 0) ∧

      (∀ v n i, st v (C (v + 1) n i) = C v n i) ∧
      (∀ v m i, C v (p ^ v * m) i =
        MvFormalGroup.adicEval (Ideal.span {(p : E v)}) (C v (p ^ v)) (Φ.nthSeries m i)) ∧

      (∀ v n i,
        MvFormalGroup.adicEval (Ideal.span {(p : E v ⊗[𝓞] E v)})
          (Sum.elim (fun j => Coalgebra.comul (R := 𝓞) (C v n j))
            (fun j => MvFormalGroup.adicEval (Ideal.span {(p : E v ⊗[𝓞] E v)}) (c₂ v) (Φ.nthSeries n j)))
          (Φ.toPowerSeries i) =
        MvFormalGroup.adicEval (Ideal.span {(p : E v ⊗[𝓞] E v)})
          (Sum.elim (fun j => C v n j ⊗ₜ[𝓞] (1 : E v))
            (fun j => MvFormalGroup.adicEval (Ideal.span {(p : E v ⊗[𝓞] E v)})
              (Sum.elim (fun j => (1 : E v) ⊗ₜ[𝓞] C v n j)
                (fun j => Algebra.TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (E v) n)
                  (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (E v) n) (c₂ v j)))
              (Φ.toPowerSeries j)))
          (Φ.toPowerSeries i)) := by
  classical
  obtain ⟨hst₂, hc₂p, hunit, hsymm, hcoc⟩ := hCOC

  haveI hcE : ∀ v, IsAdicComplete (Ideal.span {(p : E v)}) (E v) := fun v =>
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (E v)
  haveI hcEE : ∀ v, IsAdicComplete (Ideal.span {(p : E v ⊗[𝓞] E v)}) (E v ⊗[𝓞] E v) := fun v =>
    IsAdicComplete.of_module_finite_free_span_natCast (𝓞 := 𝓞) p (E v ⊗[𝓞] E v)
  have hpE : ∀ v, (p : E v) ∈ nonZeroDivisors (E v) := fun v => natCast_mem_nonZeroDivisors hp (E v)
  have hpEE : ∀ v, (p : E v ⊗[𝓞] E v) ∈ nonZeroDivisors (E v ⊗[𝓞] E v) := fun v =>
    natCast_mem_nonZeroDivisors hp (E v ⊗[𝓞] E v)

  refine ⟨fun v n => (defect (cpt p Φ (E v) (c₂ v) (hc₂p v) (E v)) n (WithConv.toConv (AlgHom.id 𝓞 (E v)))).val,
    fun v i => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v n i
    show (defect (cpt p Φ (E v) (c₂ v) (hc₂p v) (E v)) (n + 1) (WithConv.toConv (AlgHom.id 𝓞 (E v)))).val i = _
    rw [defect_succ, Points.val_add]
    congr 1
    refine congrArg _ (funext fun j => ?_)
    rw [cpt_val, ← Algebra.TensorProduct.lmul'_comp_map]
    rfl
  ·
    intro v n i
    exact dft_val_mem p Φ (E v) (c₂ v) (hc₂p v) (E v) n _ i
  ·
    intro v n i
    have h := map_dft p Φ (E v) (c₂ v) (hc₂p v) (g := E v) (g' := 𝓞) (Bialgebra.counitAlgHom 𝓞 (E v)) n
      (WithConv.toConv (AlgHom.id 𝓞 (E v)))
    have h1 : WithConv.toConv ((Bialgebra.counitAlgHom 𝓞 (E v)).comp
        (WithConv.ofConv (WithConv.toConv (AlgHom.id 𝓞 (E v))))) = (1 : WithConv (E v →ₐ[𝓞] 𝓞)) := by
      apply WithConv.ofConv_injective
      rw [ofConv_one]
      refine AlgHom.ext fun x => ?_
      change Coalgebra.counit (R := 𝓞) x = algebraMap 𝓞 𝓞 (Coalgebra.counit (R := 𝓞) x)
      rw [Algebra.algebraMap_self, RingHom.id_apply]
    have hone : ∀ a, cpt p Φ (E v) (c₂ v) (hc₂p v) 𝓞 1 a = 0 := fun a =>
      Points.ext (funext fun j => by rw [cpt_val, ofConv_one]; exact (hunit 𝓞 hp inferInstance v a.ofConv j).2)
    rw [h1, defect_one hone] at h
    exact congrArg (fun P : MvFormalGroup.Points Φ 𝓞 (Ideal.span {(p : 𝓞)}) => P.val i) h
  ·
    intro v n i
    have h := map_dft p Φ (E (v + 1)) (c₂ (v + 1)) (hc₂p (v + 1)) (g := E (v + 1)) (g' := E v)
      (st v : E (v + 1) →ₐ[𝓞] E v) n (WithConv.toConv (AlgHom.id 𝓞 (E (v + 1))))
    have h2 := dft_comp p Φ (g := E v) (c₂ v) (hc₂p v) (c₂ (v + 1)) (hc₂p (v + 1)) (st v) (hst₂ v) n
      (WithConv.toConv (AlgHom.id 𝓞 (E v)))
    have e : WithConv.toConv ((st v : E (v + 1) →ₐ[𝓞] E v).comp
        (WithConv.ofConv (WithConv.toConv (AlgHom.id 𝓞 (E (v + 1)))))) =
        WithConv.toConv ((WithConv.ofConv (WithConv.toConv (AlgHom.id 𝓞 (E v)))).comp
          (st v : E (v + 1) →ₐ[𝓞] E v)) := by
      congr 1
    rw [e, h2] at h
    exact congrArg (fun P : MvFormalGroup.Points Φ (E v) (Ideal.span {(p : E v)}) => P.val i) h
  ·
    intro v m i
    have hcyc := isCocycle p Φ (E v) (c₂ v) (hc₂p v) (E v) (fun f j => (hunit (E v) (hpE v) (hcE v) v f j).2)
      (hsymm (E v) (hpE v) (hcE v) v) (hcoc (E v) (hpE v) (hcE v) v)
    have hkill : (WithConv.toConv (AlgHom.id 𝓞 (E v))) ^ (p ^ v) = 1 :=
      toConv_id_pow_eq_one (st v) (hst v) (p ^ v) (hkerE v)
    have h : defect (cpt p Φ (E v) (c₂ v) (hc₂p v) (E v)) (p ^ v * m) (WithConv.toConv (AlgHom.id 𝓞 (E v))) =
        m • defect (cpt p Φ (E v) (c₂ v) (hc₂p v) (E v)) (p ^ v) (WithConv.toConv (AlgHom.id 𝓞 (E v))) :=
      defect_mul_of_pow_eq_one hcyc _ _ hkill m
    have h' := congrArg (fun P : MvFormalGroup.Points Φ (E v) (Ideal.span {(p : E v)}) => P.val i) h
    simp only [Points.val_nsmul] at h'
    exact h'
  ·
    intro v n i
    have hcyc := isCocycle p Φ (E v) (c₂ v) (hc₂p v) (E v ⊗[𝓞] E v)
      (fun f j => (hunit (E v ⊗[𝓞] E v) (hpEE v) (hcEE v) v f j).2)
      (hsymm (E v ⊗[𝓞] E v) (hpEE v) (hcEE v) v) (hcoc (E v ⊗[𝓞] E v) (hpEE v) (hcEE v) v)
    have key := defect_mul_add_nsmul hcyc
      (WithConv.toConv (Algebra.TensorProduct.includeLeft : E v →ₐ[𝓞] E v ⊗[𝓞] E v))
      (WithConv.toConv (Algebra.TensorProduct.includeRight : E v →ₐ[𝓞] E v ⊗[𝓞] E v)) n

    have hprod : WithConv.toConv (Algebra.TensorProduct.includeLeft : E v →ₐ[𝓞] E v ⊗[𝓞] E v) *
        WithConv.toConv (Algebra.TensorProduct.includeRight : E v →ₐ[𝓞] E v ⊗[𝓞] E v) =
        WithConv.toConv ((Bialgebra.comulAlgHom 𝓞 (E v)).comp
          (WithConv.ofConv (WithConv.toConv (AlgHom.id 𝓞 (E v))))) := by
      apply WithConv.ofConv_injective
      rw [ofConv_mul]
      change (Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : E v →ₐ[𝓞] E v ⊗[𝓞] E v)
        (Algebra.TensorProduct.includeRight : E v →ₐ[𝓞] E v ⊗[𝓞] E v) _).comp _ =
        (Bialgebra.comulAlgHom 𝓞 (E v)).comp (AlgHom.id 𝓞 (E v))
      rw [Algebra.TensorProduct.lift_includeLeft_includeRight, AlgHom.id_comp, AlgHom.comp_id]
    have e1 : (defect (cpt p Φ (E v) (c₂ v) (hc₂p v) (E v ⊗[𝓞] E v)) n
        (WithConv.toConv (Algebra.TensorProduct.includeLeft : E v →ₐ[𝓞] E v ⊗[𝓞] E v) *
          WithConv.toConv (Algebra.TensorProduct.includeRight : E v →ₐ[𝓞] E v ⊗[𝓞] E v))).val =
        fun j => Coalgebra.comul (R := 𝓞)
          ((defect (cpt p Φ (E v) (c₂ v) (hc₂p v) (E v)) n (WithConv.toConv (AlgHom.id 𝓞 (E v)))).val j) := by
      rw [hprod, ← map_dft]
      rfl
    have e2 : (n • cpt p Φ (E v) (c₂ v) (hc₂p v) (E v ⊗[𝓞] E v)
        (WithConv.toConv (Algebra.TensorProduct.includeLeft : E v →ₐ[𝓞] E v ⊗[𝓞] E v))
        (WithConv.toConv (Algebra.TensorProduct.includeRight : E v →ₐ[𝓞] E v ⊗[𝓞] E v))).val =
        fun j => MvFormalGroup.adicEval (Ideal.span {(p : E v ⊗[𝓞] E v)}) (c₂ v) (Φ.nthSeries n j) := by
      rw [Points.val_nsmul]
      have hc : (cpt p Φ (E v) (c₂ v) (hc₂p v) (E v ⊗[𝓞] E v)
          (WithConv.toConv (Algebra.TensorProduct.includeLeft : E v →ₐ[𝓞] E v ⊗[𝓞] E v))
          (WithConv.toConv (Algebra.TensorProduct.includeRight : E v →ₐ[𝓞] E v ⊗[𝓞] E v))).val = c₂ v := by
        funext j
        rw [cpt_val]
        change Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : E v →ₐ[𝓞] E v ⊗[𝓞] E v)
          (Algebra.TensorProduct.includeRight : E v →ₐ[𝓞] E v ⊗[𝓞] E v) _ (c₂ v j) = c₂ v j
        rw [Algebra.TensorProduct.lift_includeLeft_includeRight, AlgHom.id_apply]
      rw [hc]
    have e3 : (defect (cpt p Φ (E v) (c₂ v) (hc₂p v) (E v ⊗[𝓞] E v)) n
        (WithConv.toConv (Algebra.TensorProduct.includeLeft : E v →ₐ[𝓞] E v ⊗[𝓞] E v))).val =
        fun j => (defect (cpt p Φ (E v) (c₂ v) (hc₂p v) (E v)) n (WithConv.toConv (AlgHom.id 𝓞 (E v)))).val j ⊗ₜ[𝓞]
          (1 : E v) := by
      have : WithConv.toConv (Algebra.TensorProduct.includeLeft : E v →ₐ[𝓞] E v ⊗[𝓞] E v) =
          WithConv.toConv ((Algebra.TensorProduct.includeLeft : E v →ₐ[𝓞] E v ⊗[𝓞] E v).comp
            (WithConv.ofConv (WithConv.toConv (AlgHom.id 𝓞 (E v))))) := by
        congr 1
      rw [this, ← map_dft]
      rfl
    have e4 : (defect (cpt p Φ (E v) (c₂ v) (hc₂p v) (E v ⊗[𝓞] E v)) n
        (WithConv.toConv (Algebra.TensorProduct.includeRight : E v →ₐ[𝓞] E v ⊗[𝓞] E v))).val =
        fun j => (1 : E v) ⊗ₜ[𝓞]
          (defect (cpt p Φ (E v) (c₂ v) (hc₂p v) (E v)) n (WithConv.toConv (AlgHom.id 𝓞 (E v)))).val j := by
      have : WithConv.toConv (Algebra.TensorProduct.includeRight : E v →ₐ[𝓞] E v ⊗[𝓞] E v) =
          WithConv.toConv ((Algebra.TensorProduct.includeRight : E v →ₐ[𝓞] E v ⊗[𝓞] E v).comp
            (WithConv.ofConv (WithConv.toConv (AlgHom.id 𝓞 (E v))))) := by
        congr 1
      rw [this, ← map_dft]
      rfl
    have e5 : (cpt p Φ (E v) (c₂ v) (hc₂p v) (E v ⊗[𝓞] E v)
        (WithConv.toConv (Algebra.TensorProduct.includeLeft : E v →ₐ[𝓞] E v ⊗[𝓞] E v) ^ n)
        (WithConv.toConv (Algebra.TensorProduct.includeRight : E v →ₐ[𝓞] E v ⊗[𝓞] E v) ^ n)).val =
        fun j => Algebra.TensorProduct.map (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (E v) n)
          (PDivisibleGroup.Hopf.nsmulAlgHom 𝓞 (E v) n) (c₂ v j) := by
      funext j
      rw [PDivisibleGroup.Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom,
        PDivisibleGroup.Hopf.toConv_pow_eq_toConv_comp_nsmulAlgHom, cpt_val]
      exact lift_includeLeft_comp_includeRight_comp_apply _ _ _
    have val_add' : ∀ x y : MvFormalGroup.Points Φ (E v ⊗[𝓞] E v) (Ideal.span {(p : E v ⊗[𝓞] E v)}),
        (x + y).val = fun k => MvFormalGroup.adicEval (Ideal.span {(p : E v ⊗[𝓞] E v)}) (Sum.elim x.val y.val)
          (Φ.toPowerSeries k) := fun x y => funext (Points.val_add x y)
    have h' := congrArg (fun P : MvFormalGroup.Points Φ (E v ⊗[𝓞] E v) (Ideal.span {(p : E v ⊗[𝓞] E v)}) =>
      P.val i) key
    simp only [val_add'] at h'
    rw [e1, e2, e3, e4, e5] at h'
    exact h'

end S_MvFormalGroup_exists_powerDefect_map_comul_eq_adicEval_of_cocycle
end P2MW
export P2MW.S_MvFormalGroup_exists_powerDefect_map_comul_eq_adicEval_of_cocycle (solution)
