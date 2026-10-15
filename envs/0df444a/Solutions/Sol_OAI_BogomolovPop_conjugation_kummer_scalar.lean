-- Prove2me | solution 1 for OAI.BogomolovPop.conjugation_kummer_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:40:16.813204+00:00
-- url     : https://prove2.me/submissions/f42adec8-2e5d-4aa9-8eb4-b01100e0c5bb

-- Generated from openai/math@1581d4c lean/OAI/Algebra/BogomolovPop/Kummer.lean:L627-L692
-- (upload_full_project.md Phase 4): solution for node OAI.BogomolovPop.conjugation_kummer_scalar. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BogomolovPopInjectivity
import Definitions.Def_OAI_Algebra_BogomolovPop_Foundations
import Definitions.Def_OAI_Algebra_BogomolovPop_Canonical
import Definitions.Def_OAI_Algebra_BogomolovPop_PowerCompletion
import Definitions.Def_OAI_Algebra_BogomolovPop_Kummer

-- ---- from OAI.Algebra.BogomolovPop.Kummer ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

/-! Tate bases, Kummer characters and scalar conjugation. -/

noncomputable section
open scoped Topology

noncomputable section
namespace BogomolovPop
open scoped Topology
variable {F : Type*} [Field F]
end BogomolovPop
noncomputable section
namespace BogomolovPop
variable {A : Type*} [Field A]

lemma primitiveLevel_nonempty [IsAlgClosed A] (ell e : ℕ) (hchar : (ell : A) ≠ 0) :
    Nonempty (PrimitiveLevel (A := A) ell e) := by
  have : NeZero (ell : A) := ⟨hchar⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot A (ell ^ e)
  have hn : ell ^ e ≠ 0 := by
    have : ell ≠ 0 := by intro h; simp [h] at hchar
    exact pow_ne_zero _ this
  obtain ⟨u, hu⟩ := hz.isUnit hn
  have hp : IsPrimitiveRoot u (ell ^ e) := by
    rw [← IsPrimitiveRoot.coe_units_iff, hu]
    exact hz
  exact ⟨⟨⟨u, hp.pow_eq_one⟩, hp⟩⟩

lemma primitiveDown_comp (ell : ℕ) (hell : 0 < ell) (e n m : ℕ)
    (hen : e ≤ n) (hnm : n ≤ m) (z : PrimitiveLevel (A := A) ell m) :
    primitiveDown ell hell e n hen (primitiveDown ell hell n m hnm z) =
      primitiveDown ell hell e m (hen.trans hnm) z := by
  apply Subtype.ext
  apply Subtype.ext
  change ((z.val : Aˣ) ^ (ell ^ (m-n))) ^ (ell ^ (n-e)) = _
  rw [← pow_mul, ← pow_add, show m-n+(n-e) = m-e by omega]
  rfl

theorem exists_compatible_primitive [IsAlgClosed A] (ell : ℕ) (hell : 0 < ell)
    (hchar : (ell : A) ≠ 0) :
    ∃ z : ℕ → Aˣ, (∀ e, IsPrimitiveRoot (z e) (ell ^ e)) ∧
      ∀ e, z (e+1) ^ ell = z e := by
  classical
  let : ∀ e, TopologicalSpace (PrimitiveLevel (A := A) ell e) := fun _ => ⊥
  let : ∀ e, DiscreteTopology (PrimitiveLevel (A := A) ell e) := fun _ => ⟨rfl⟩
  let : ∀ e, NeZero (ell ^ e) := fun e => ⟨pow_ne_zero _ hell.ne'⟩
  let : ∀ e, Nonempty (PrimitiveLevel (A := A) ell e) := fun e => primitiveLevel_nonempty ell e hchar
  let T := ∀ e, PrimitiveLevel (A := A) ell e
  let s (e : ℕ) : Set T :=
    {z | primitiveDown ell hell e (e+1) (Nat.le_succ e) (z (e+1)) = z e}
  have hs (e : ℕ) : IsClosed (s e) :=
    isClosed_eq ((continuous_of_discreteTopology : Continuous
      (primitiveDown (A := A) ell hell e (e+1) (Nat.le_succ e))).comp (continuous_apply (e+1))) (continuous_apply e)
  have hf (u : Finset ℕ) : (Set.univ ∩ ⋂ e ∈ u, s e).Nonempty := by
    let n := u.sup Nat.succ
    let a : PrimitiveLevel (A := A) ell n := Classical.choice inferInstance
    let z : T := fun e => if h : e ≤ n then primitiveDown ell hell e n h a
      else Classical.choice inferInstance
    refine ⟨z, Set.mem_univ _, Set.mem_iInter.mpr fun e => Set.mem_iInter.mpr fun he => ?_⟩
    have hn : e+1 ≤ n := Finset.le_sup (f := Nat.succ) he
    change primitiveDown ell hell e (e+1) (Nat.le_succ e) (z (e+1)) = z e
    simp only [z, dite_eq_left hn, dite_eq_left ((Nat.le_succ e).trans hn)]
    exact primitiveDown_comp ell hell e (e+1) n (Nat.le_succ e) hn a
  obtain ⟨z, _, hz⟩ := isCompact_univ.inter_iInter_nonempty s hs hf
  refine ⟨fun e => (z e).val.val, fun e => (z e).property, fun e => ?_⟩
  have he := congrArg (fun z : PrimitiveLevel (A := A) ell e => z.val.val) (Set.mem_iInter.mp hz e)
  simpa [primitiveDown] using he

end BogomolovPop

namespace BogomolovPop
open scoped Topology
open Filter

variable {ell : ℕ} [Fact ell.Prime]

theorem root_continuous_padic_toZModPow (n : ℕ) :
    Continuous (PadicInt.toZModPow (p := ell) n) := by
  apply continuous_of_continuousAt_zero
  rw [ContinuousAt, map_zero, (nhds_discrete (ZMod (ell ^ n))), tendsto_pure]
  have hpos : 0 < (ell : ℝ) := Nat.cast_pos.mpr (Fact.out : ell.Prime).pos
  have hr : (ell : ℝ) ^ (-(n : ℤ)) ≠ 0 := zpow_ne_zero _ (ne_of_gt hpos)
  have hb := (IsUltrametricDist.isOpen_closedBall (0 : PadicInt ell) hr).mem_nhds
    (Metric.mem_closedBall_self (le_of_lt (by positivity : (0 : ℝ) < ell ^ (-(n : ℤ)))))
  filter_upwards [hb] with x hx
  apply RingHom.mem_ker.mp
  rw [PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  simpa only [Metric.mem_closedBall, dist_zero_right] using hx

end BogomolovPop

namespace BogomolovPop
variable {F : Type*} [Field F] {ell : ℕ} [Fact ell.Prime]

lemma padicToTate_continuous (z : ℕ → (AlgebraicClosure F)ˣ)
    (hz : ∀ e, IsPrimitiveRoot (z e) (ell ^ e))
    (hc : ∀ e, z (e+1) ^ ell = z e) : Continuous (padicToTate z hz hc) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro e
  exact (continuous_of_discreteTopology : Continuous (zmodRootEquiv (hz e))).comp
    (continuous_ofAdd.comp ((root_continuous_padic_toZModPow e).comp
      continuous_toAdd))

lemma padicToTate_surjective (z : ℕ → (AlgebraicClosure F)ˣ)
    (hz : ∀ e, IsPrimitiveRoot (z e) (ell ^ e))
    (hc : ∀ e, z (e+1) ^ ell = z e) : Function.Surjective (padicToTate z hz hc) := by
  intro t
  let s (e : ℕ) : Set (Multiplicative (PadicInt ell)) := {a | (padicToTate z hz hc a).val e = t.val e}
  have hs (e : ℕ) : IsClosed (s e) :=
    isClosed_eq ((continuous_apply e).comp (continuous_subtype_val.comp (padicToTate_continuous z hz hc))) continuous_const
  have hn (e : ℕ) : (s e).Nonempty := by
    let i := ((zmodRootEquiv (hz e)).symm (t.val e)).toAdd
    refine ⟨Multiplicative.ofAdd (i.val : PadicInt ell), ?_⟩
    change zmodRootEquiv (hz e) (Multiplicative.ofAdd (PadicInt.toZModPow e (i.val : PadicInt ell))) = t.val e
    rw [map_natCast, ZMod.natCast_zmod_val]
    exact (zmodRootEquiv (hz e)).apply_symm_apply (t.val e)
  have hm : Antitone s := antitone_nat_of_succ_le (fun e a ha => by
    change (padicToTate z hz hc a).val e = t.val e
    rw [← (padicToTate z hz hc a).property e, ← t.property e, ha])
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    s (fun e => hm (Nat.le_succ e)) hn ((hs 0).isCompact) hs
  exact ⟨a, Subtype.ext (funext fun e => Set.mem_iInter.mp ha e)⟩

end BogomolovPop

namespace BogomolovPop
lemma root_scalar_exists (ell : ℕ) [Fact ell.Prime]
    (F : Type*) [Field F] (hchar : (ell : F) ≠ 0)
    (σ : AlgebraicClosure F ≃+* AlgebraicClosure F) :
    ∃ a : PadicInt ell, ∀ n : ℕ, ∀ z : (AlgebraicClosure F)ˣ,
      z ^ (ell ^ n) = 1 → Units.map σ.toMonoidHom z = z ^ a.appr n := by
  have hc : (ell : AlgebraicClosure F) ≠ 0 := by
    simpa only [map_natCast] using (map_ne_zero (algebraMap F (AlgebraicClosure F))).mpr hchar
  obtain ⟨z, hz, hcompat⟩ := exists_compatible_primitive ell (Nat.Prime.pos Fact.out) hc
  let t : TateModule ell F := ⟨fun n => ⟨Units.map σ.toMonoidHom (z n), by
    rw [mem_rootsOfUnity, ← map_pow, (hz n).pow_eq_one, map_one]⟩,
    fun n => Subtype.ext (by change _ ^ ell = _; rw [← map_pow, hcompat n])⟩
  obtain ⟨a, ha⟩ := padicToTate_surjective z hz hcompat t
  have haz (n : ℕ) : Units.map σ.toMonoidHom (z n) = z n ^ a.toAdd.appr n := by
    have he := congrArg (fun v : TateModule ell F => (v.val n : (AlgebraicClosure F)ˣ)) ha
    change (zmodRootEquiv (hz n) (Multiplicative.ofAdd
      (PadicInt.toZModPow n a.toAdd)) : (AlgebraicClosure F)ˣ) = _ at he
    rw [show PadicInt.toZModPow n a.toAdd = (a.toAdd.appr n : ZMod (ell ^ n)) by rfl,
      zmodRootEquiv_nat] at he
    exact he.symm
  refine ⟨a.toAdd, fun n w hw => ?_⟩
  let : NeZero (ell ^ n) := ⟨pow_ne_zero _ (Nat.Prime.ne_zero Fact.out)⟩
  obtain ⟨i, hi⟩ := (zmodRootEquiv (hz n)).surjective ⟨w, hw⟩
  have he := congrArg (fun v : rootsOfUnity (ell ^ n) (AlgebraicClosure F) =>
    (v : (AlgebraicClosure F)ˣ)) hi
  rw [show i = Multiplicative.ofAdd i.toAdd by rfl, zmodRootEquiv_val] at he
  change z n ^ i.toAdd.val = w at he
  rw [← he, map_pow, haz, ← pow_mul, ← pow_mul, Nat.mul_comm]

theorem closure_root_scalar (ell : ℕ) [Fact ell.Prime]
    (F : Type*) [Field F] (hchar : (ell : F) ≠ 0)
    (σ : AlgebraicClosure F ≃+* AlgebraicClosure F) :
    ∃ u : (PadicInt ell)ˣ, ∀ n : ℕ, ∀ z : AlgebraicClosure F,
      z ^ (ell ^ n) = 1 → σ z = z ^ (u : PadicInt ell).appr n := by
  obtain ⟨a, ha⟩ := root_scalar_exists ell F hchar σ
  obtain ⟨b, hb⟩ := root_scalar_exists ell F hchar σ.symm
  have hab : a * b = 1 := by
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    let : NeZero (ell ^ n) := ⟨pow_ne_zero _ (Nat.Prime.ne_zero Fact.out)⟩
    have hc : (ell : AlgebraicClosure F) ≠ 0 := by
      simpa only [map_natCast] using (map_ne_zero (algebraMap F (AlgebraicClosure F))).mpr hchar
    obtain ⟨z, hz⟩ := primitiveLevel_nonempty (A := AlgebraicClosure F) ell n hc
    have he : (z : (AlgebraicClosure F)ˣ) ^ (a.appr n * b.appr n) = z := by
      rw [pow_mul, ← ha n _ hz.pow_eq_one, ← hb n _ (by rw [← map_pow, hz.pow_eq_one, map_one])]
      apply Units.ext
      exact σ.symm_apply_apply _
    have hh := (zmodRootEquiv hz).injective (show
      zmodRootEquiv hz (Multiplicative.ofAdd ((a.appr n * b.appr n : ℕ) : ZMod (ell ^ n))) =
      zmodRootEquiv hz (Multiplicative.ofAdd (1 : ZMod (ell ^ n))) by
        apply Subtype.ext
        rw [zmodRootEquiv_nat]
        have hh1 := zmodRootEquiv_nat hz 1
        simp only [Nat.cast_one, pow_one] at hh1
        exact he.trans hh1.symm
        )
    change (PadicInt.toZModPow n) (a * b) = (PadicInt.toZModPow n) 1
    rw [map_mul, map_one]
    simpa only [toAdd_ofAdd, Nat.cast_mul, PadicInt.toZModPow, PadicInt.toZModHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] using congrArg Multiplicative.toAdd hh
  refine ⟨Units.mkOfMulEqOne a b hab, fun n z hz => ?_⟩
  have hz0 : z ≠ 0 := by
    intro he
    rw [he, zero_pow (pow_ne_zero _ (Nat.Prime.ne_zero Fact.out))] at hz
    exact zero_ne_one hz
  exact congrArg Units.val (ha n (Units.mk0 z hz0) (Units.ext hz))
end BogomolovPop

noncomputable section
namespace BogomolovPop

open Polynomial

theorem fixed_separable_mem_base {F A : Type*} [Field F] [Field A] [Algebra F A]
    [Normal F A] {x : A} (hx : IsSeparable F x)
    (hfix : ∀ σ : A ≃ₐ[F] A, σ x = x) : x ∈ Set.range (algebraMap F A) := by
  let S := separableClosure F A
  let z : S := ⟨x, hx⟩
  have hz : z ∈ Set.range (algebraMap F S) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed z).mpr fun τ => by
      obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := A) (K₁ := S) τ
      apply Subtype.val_injective
      exact (AlgEquiv.restrictNormal_commutes σ S z).trans (hfix σ)
  obtain ⟨f, hf⟩ := hz
  exact ⟨f, congrArg Subtype.val hf⟩

variable {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]

theorem kummerRoot_isSeparable (n : ℕ) (hn : 0 < n) (hchar : (n : F) ≠ 0) (f : Fˣ) :
    IsSeparable F (kummerRoot n hn f : AlgebraicClosure F) := by
  apply (Polynomial.separable_X_pow_sub_C (f : F) hchar f.ne_zero).of_dvd
  exact minpoly.dvd F _ (by simp [kummerRoot_pow])

theorem kummerPairing_eq_one_iff (n : ℕ) (hn : 0 < n) (hchar : (n : F) ≠ 0) (f : Fˣ) :
    kummerPairing (k := k) n hn f = 1 ↔ ∃ g : Fˣ, g ^ n = f := by
  constructor
  · intro hf
    have hfix (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
        σ (kummerRoot n hn f : AlgebraicClosure F) = kummerRoot n hn f := by
      have hh := congrArg (fun χ => ((χ σ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F)) hf
      change σ (kummerRoot n hn f : AlgebraicClosure F) / kummerRoot n hn f = 1 at hh
      exact (div_eq_one_iff_eq (kummerRoot n hn f).ne_zero).mp hh
    obtain ⟨g, hg⟩ := fixed_separable_mem_base (kummerRoot_isSeparable n hn hchar f) hfix
    have hg0 : g ≠ 0 := by
      intro he
      apply (kummerRoot n hn f).ne_zero
      rw [← hg, he, map_zero]
    refine ⟨Units.mk0 g hg0, Units.ext ((algebraMap F (AlgebraicClosure F)).injective ?_)⟩
    simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hg] using kummerRoot_pow n hn f
  · rintro ⟨g, rfl⟩
    ext σ
    change ((kummerCharacter (k := k) n hn (g ^ n) σ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) = 1
    rw [kummerCharacter_apply_of_root n hn (g ^ n) σ (Units.map (algebraMap F (AlgebraicClosure F)) g)
      (by simp)]
    change σ (algebraMap F (AlgebraicClosure F) (g : F)) / algebraMap F (AlgebraicClosure F) (g : F) = 1
    rw [σ.commutes, div_self ((_root_.map_ne_zero _).mpr g.ne_zero)]

theorem kummerPiA_continuous (ell e : ℕ) (hell : 0 < ell) (f : Fˣ) :
    Continuous (kummerPiA (k := k) ell e hell f) := by
  apply continuous_coinduced_dom.mpr
  exact kummerProEll_continuous ell e hell f

theorem kummerPiA_eq_one_iff (ell e : ℕ) (hell : 0 < ell) (hchar : (ell : F) ≠ 0) (f : Fˣ) :
    kummerPiA (k := k) ell e hell f = 1 ↔ ∃ g : Fˣ, g ^ (ell ^ e) = f := by
  have hc : ((ell ^ e : ℕ) : F) ≠ 0 := by simpa using pow_ne_zero e hchar
  rw [← kummerPairing_eq_one_iff (k := k) (ell ^ e) (pow_pos hell e) hc f]
  constructor
  · intro h
    apply MonoidHom.ext
    intro σ
    exact DFunLike.congr_fun h (absoluteToPiA ell F σ)
  · intro h
    apply MonoidHom.ext
    intro x
    obtain ⟨σ, rfl⟩ := absoluteToPiA_surjective (F := F) ell x
    exact DFunLike.congr_fun h σ

end BogomolovPop

namespace BogomolovPop
open scoped Topology
open Filter
lemma torsion_appr_eventually {G : Type*} [CommGroup G] (ell : ℕ) [Fact ell.Prime]
    (a : PadicInt ell) (e : ℕ) (x : G) (hx : x ^ (ell ^ e) = 1) :
    ∀ᶠ n in atTop, x ^ a.appr n = x ^ a.appr e := by
  filter_upwards [eventually_ge_atTop e] with n hn
  obtain ⟨c, hc⟩ := a.dvd_appr_sub_appr e n hn
  have he : a.appr n = a.appr e + ell ^ e * c := by
    have := a.appr_mono hn
    omega
  rw [he, pow_add, pow_mul, hx, one_pow, mul_one]

lemma kummerPiA_scalar_limit (ell : ℕ) [Fact ell.Prime]
    {k F : Type*} [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    (u : PadicInt ell) (σ τ : PiA ell F)
    (h : Tendsto (fun n : ℕ => σ ^ u.appr n) atTop (nhds τ)) (e : ℕ) (f : Fˣ) :
    kummerPiA (k := k) ell e (Nat.Prime.pos Fact.out) f τ =
      kummerPiA (k := k) ell e (Nat.Prime.pos Fact.out) f σ ^ u.appr e := by
  let χ := kummerPiA (k := k) ell e (Nat.Prime.pos Fact.out) f
  have hc : Tendsto (fun n : ℕ => χ (σ ^ u.appr n)) atTop (nhds (χ τ)) :=
    (kummerPiA_continuous ell e (Nat.Prime.pos Fact.out) f).continuousAt.tendsto.comp h
  have hd : Tendsto (fun n : ℕ => χ (σ ^ u.appr n)) atTop (nhds (χ σ ^ u.appr e)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [torsion_appr_eventually ell u e (χ σ)
      (Subtype.ext (χ σ).property)] with n hn
    simpa only [map_pow] using hn.symm
  exact tendsto_nhds_unique hc hd

lemma kummerPiA_class_eq {k F : Type*} [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    (ell e : ℕ) (hell : 0 < ell) (hchar : (ell : F) ≠ 0) {f g : Fˣ}
    (h : ∀ σ, kummerPiA (k := k) ell e hell f σ = kummerPiA (k := k) ell e hell g σ) :
    PowerClass.mk (ell ^ e) f = PowerClass.mk (ell ^ e) g := by
  rw [← div_eq_one, ← map_div, PowerClass.mk_eq_one]
  apply (kummerPiA_eq_one_iff (k := k) ell e hell hchar (f / g)).mp
  change kummerPiAPairing (k := k) ell e hell (f / g) = 1
  rw [map_div, div_eq_one]
  exact MonoidHom.ext h

theorem conjugation_kummer_scalar (ell : ℕ) [Fact ell.Prime]
    (k F : Type*) [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    (hchar : (ell : F) ≠ 0) (φ : F →+* F)
    (β : AlgebraicClosure F ≃+* AlgebraicClosure F)
    (hβ : ∀ x : F, β (algebraMap F (AlgebraicClosure F) x) =
      algebraMap F (AlgebraicClosure F) (φ x))
    (u : (PadicInt ell)ˣ)
    (hg : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      ∃ τ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
        (∀ x, β (τ x) = σ (β x)) ∧
        Tendsto (fun n : ℕ => absoluteToPiA ell F σ ^ (u : PadicInt ell).appr n)
          atTop (nhds (absoluteToPiA ell F τ))) :
    ∃ a : (PadicInt ell)ˣ, ∀ f : Fˣ,
      KummerScalarLevels ell (a : PadicInt ell) f (Units.map φ.toMonoidHom f) := by
  obtain ⟨v, hv⟩ := closure_root_scalar ell F hchar β
  refine ⟨v * u, fun f e => ?_⟩
  rw [← map_pow]
  apply kummerPiA_class_eq (k := k) ell e (Nat.Prime.pos Fact.out) hchar
  intro γ
  obtain ⟨σ, rfl⟩ := absoluteToPiA_surjective (F := F) ell γ
  change AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F at σ
  obtain ⟨τ, hτ, hlim⟩ := hg σ
  let r := kummerRoot (ell ^ e) (pow_pos (Nat.Prime.pos Fact.out) e) f
  have hn : 0 < ell ^ e := pow_pos (Nat.Prime.pos Fact.out) e
  have hr : ((Units.map β.toMonoidHom r : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) ^ (ell ^ e) =
      algebraMap F (AlgebraicClosure F) (Units.map φ.toMonoidHom f : F) := by
    change (β (r : AlgebraicClosure F)) ^ _ = _
    rw [← map_pow, kummerRoot_pow, hβ]
    rfl
  have hroot := kummerCharacter_apply_of_root (k := k) (ell ^ e) hn
    (Units.map φ.toMonoidHom f) σ (Units.map β.toMonoidHom r) hr
  have hleft := kummerCharacter_apply_of_root (k := k) (ell ^ e) hn f τ r (kummerRoot_pow _ _ f)
  have hright := kummerPiA_scalar_limit (k := k) ell (u : PadicInt ell)
    (absoluteToPiA ell F σ) (absoluteToPiA ell F τ) hlim e f
  have hv' := hv e (τ (r : AlgebraicClosure F) / r) (by
    rw [div_pow, ← map_pow, kummerRoot_pow, τ.commutes,
      div_self ((map_ne_zero (algebraMap F (AlgebraicClosure F))).mpr f.ne_zero)])
  have heq : kummerPiA (k := k) ell e (Nat.Prime.pos Fact.out)
      (Units.map φ.toMonoidHom f) (absoluteToPiA ell F σ) =
      (kummerPiA (k := k) ell e (Nat.Prime.pos Fact.out) f
        (absoluteToPiA ell F σ)) ^ ((u : PadicInt ell).appr e * (v : PadicInt ell).appr e) := by
    apply Subtype.ext
    apply Units.ext
    change ((kummerCharacter (k := k) (ell ^ e) hn (Units.map φ.toMonoidHom f) σ :
      (AlgebraicClosure F)ˣ) : AlgebraicClosure F) = _
    rw [hroot]
    change σ (β (r : AlgebraicClosure F)) / β (r : AlgebraicClosure F) = _
    rw [← hτ, ← map_div₀, hv']
    rw [← hleft]
    have hh := congrArg (fun z : rootsOfUnity (ell ^ e) (AlgebraicClosure F) =>
      ((z : (AlgebraicClosure F)ˣ) : AlgebraicClosure F)) hright
    change ((kummerCharacter (k := k) (ell ^ e) hn f τ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) = _ at hh
    rw [hh]
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, pow_mul]
  rw [heq]
  change _ = kummerPiAPairing (k := k) ell e (Nat.Prime.pos Fact.out)
    (f ^ (↑(v * u) : PadicInt ell).appr e) (absoluteToPiA ell F σ)
  rw [map_pow, MonoidHom.pow_apply]
  let ζ := kummerPiA (k := k) ell e (Nat.Prime.pos Fact.out) f (absoluteToPiA ell F σ)
  have hh : (((u : PadicInt ell).appr e * (v : PadicInt ell).appr e : ℕ) : ZMod (ell ^ e)) =
      ((↑(v * u) : PadicInt ell).appr e : ZMod (ell ^ e)) := by
    rw [Nat.cast_mul]
    change (PadicInt.toZModPow e) (u : PadicInt ell) * (PadicInt.toZModPow e) (v : PadicInt ell) = (PadicInt.toZModPow e) (↑(v * u) : PadicInt ell)
    rw [Units.val_mul, map_mul, mul_comm]
  have hd := (ZMod.natCast_eq_natCast_iff _ _ _).mp hh
  exact (pow_eq_pow_of_modEq hd (Subtype.ext ζ.property))
end BogomolovPop

end
end
end
end

end OAI

-- ---- platform node ----
open OAI OAI.BogomolovPop
open scoped Topology
open scoped Topology
open Filter

theorem solution (ell : ℕ) [Fact ell.Prime]
    (k F : Type*) [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    (hchar : (ell : F) ≠ 0) (φ : F →+* F)
    (β : AlgebraicClosure F ≃+* AlgebraicClosure F)
    (hβ : ∀ x : F, β (algebraMap F (AlgebraicClosure F) x) =
      algebraMap F (AlgebraicClosure F) (φ x))
    (u : (PadicInt ell)ˣ)
    (hg : ∀ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
      ∃ τ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
        (∀ x, β (τ x) = σ (β x)) ∧
        Tendsto (fun n : ℕ => absoluteToPiA ell F σ ^ (u : PadicInt ell).appr n)
          atTop (nhds (absoluteToPiA ell F τ))) :
    ∃ a : (PadicInt ell)ˣ, ∀ f : Fˣ,
      KummerScalarLevels ell (a : PadicInt ell) f (Units.map φ.toMonoidHom f) := by
  first
    | exact OAI.BogomolovPop.conjugation_kummer_scalar ell k F hchar φ β hβ u hg
    | exact OAI.BogomolovPop.conjugation_kummer_scalar
    | (apply OAI.BogomolovPop.conjugation_kummer_scalar <;> assumption)
    | (intros; apply OAI.BogomolovPop.conjugation_kummer_scalar <;> assumption)
