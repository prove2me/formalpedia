-- Prove2me | solution 1 for OAI.BogomolovPop.kummer_endomorphism_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T20:37:21.394687+00:00
-- url     : https://prove2.me/submissions/3ac0bdae-7fc2-40fb-a3d5-b732cddede1e

-- Generated from openai/math@1581d4c lean/OAI/Algebra/BogomolovPop/PowerCompletion.lean:L935-L962
-- (upload_full_project.md Phase 4): solution for node OAI.BogomolovPop.kummer_endomorphism_frobenius. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BogomolovPopInjectivity
import Definitions.Def_OAI_Algebra_BogomolovPop_Foundations
import Definitions.Def_OAI_Algebra_BogomolovPop_Canonical
import Definitions.Def_OAI_Algebra_BogomolovPop_PowerCompletion
import Theorems.Thm_OAI_BogomolovPop_transcendental_integer_character

-- ---- from OAI.Algebra.BogomolovPop.PowerCompletion ----
namespace OAI

/-! Multiplicative power completions, integral characters and Frobenius endomorphisms. -/

noncomputable section
open scoped Topology

noncomputable section
namespace BogomolovPop

namespace PowerClass
variable {G H I : Type*} [CommGroup G] [CommGroup H] [CommGroup I]

end PowerClass

namespace PowerCompletion
variable {ell : ℕ} {G H I : Type*} [CommGroup G] [CommGroup H] [CommGroup I]

theorem map_injective (f : G →* H)
    (hf : ∀ n, Function.Injective (PowerClass.map f (ell ^ n))) :
    Function.Injective (map (ell := ell) f) := by
  intro x y h
  apply ext
  intro n
  apply hf n
  exact congrArg (fun z : PowerCompletion ell H => z.1 n) h

end PowerCompletion
end BogomolovPop

namespace BogomolovPop
noncomputable section

namespace PowerClass
variable {G : Type*} [CommGroup G]

theorem pow_eq_one (q : ℕ) (x : PowerClass G q) : x ^ q = 1 := by
  induction x using QuotientGroup.induction_on with
  | H x => exact (map_pow (mk q) x q).symm.trans (mk_eq_one.2 ⟨x, rfl⟩)

end PowerClass

namespace PowerCompletion
variable {G : Type*} [CommGroup G] {ell : ℕ}

theorem pow_ell_eq_one (_hell : 0 < ell)
    (htors : ∀ z : G, z ^ ell = 1 → ∀ n, ∃ c : G, c ^ (ell ^ n) = z)
    (x : PowerCompletion ell G) (hx : x ^ ell = 1) : x = 1 := by
  apply ext
  intro n
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (powerSubgroup G (ell ^ (n+1)))
    (x.1 (n+1))
  change PowerClass.mk (ell ^ (n+1)) a = x.1 (n+1) at ha
  have hapow : PowerClass.mk (ell ^ (n+1)) (a ^ ell) = 1 := by
    rw [map_pow, ha]
    exact congrArg (fun y : PowerCompletion ell G => y.1 (n+1)) hx
  obtain ⟨b, hb⟩ := PowerClass.mk_eq_one.1 hapow
  have hz : (a / b ^ (ell ^ n)) ^ ell = 1 := by
    rw [div_pow, ← pow_mul, ← pow_succ, hb, div_self']
  obtain ⟨c, hc⟩ := htors _ hz n
  have hc' : (b*c) ^ (ell ^ n) = a := by
    simp only [mul_pow, hc, div_eq_mul_inv, ← mul_assoc, mul_comm, mul_inv_cancel_right]
  rw [← x.2 n, ← ha, PowerClass.reduce_mk]
  exact PowerClass.mk_eq_one.2 ⟨b*c, hc'⟩

theorem pow_eq_one (hell : ell.Prime)
    (htors : ∀ z : G, z ^ ell = 1 → ∀ n, ∃ c : G, c ^ (ell ^ n) = z)
    (x : PowerCompletion ell G) {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : x = 1 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hd : ell ∣ m
    · have hpow : (x ^ (m / ell)) ^ ell = 1 := by
        rw [← pow_mul, Nat.div_mul_cancel hd, hx]
      have hsmall : m / ell < m := Nat.div_lt_self hm hell.one_lt
      have hmdiv : 0 < m / ell := Nat.div_pos (Nat.le_of_dvd hm hd) hell.pos
      exact ih (m / ell) hsmall hmdiv (pow_ell_eq_one hell.pos htors _ hpow)
    · apply ext
      intro n
      have h1 : (x.1 n) ^ m = 1 :=
        congrArg (fun y : PowerCompletion ell G => y.1 n) hx
      have h2 := PowerClass.pow_eq_one (ell ^ n) (x.1 n)
      have hcop := ((hell.coprime_iff_not_dvd.2 hd).symm).pow_right n
      apply orderOf_eq_one_iff.1
      exact Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd
        (orderOf_dvd_iff_pow_eq_one.2 h1) (orderOf_dvd_iff_pow_eq_one.2 h2))

end PowerCompletion

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

theorem field_torsion_divisible {k F : Type*} [Field k] [IsAlgClosed k]
    [Field F] [Algebra k F] {ell : ℕ} (hell : 0 < ell)
    (z : Fˣ) (hz : z ^ ell = 1) (n : ℕ) : ∃ c : Fˣ, c ^ (ell ^ n) = z := by
  have hzalg : IsAlgebraic k (z : F) := IsAlgebraic.of_pow hell (by
    have hz' : (z : F) ^ ell = 1 := congrArg Units.val hz
    rw [hz']
    exact isAlgebraic_one)
  have hzmem : (z : F) ∈ algebraicClosure k F := mem_algebraicClosure_iff.2 hzalg
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure k F)] at hzmem
  obtain ⟨a, ha⟩ := hzmem
  change algebraMap k F a = (z : F) at ha
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a (pow_pos hell n)
  have hb0 : b ≠ 0 := by
    intro hzero
    have ha0 : a = 0 := by rw [hzero, zero_pow (by positivity)] at hb; exact hb.symm
    apply z.ne_zero
    rw [← ha, ha0, map_zero]
  refine ⟨Units.mk0 (algebraMap k F b) ((map_ne_zero _).2 hb0), Units.ext ?_⟩
  simpa only [Units.val_pow_eq_pow_val, Units.val_mk0, ← map_pow, hb] using ha

theorem field_completion_pow_eq_one {k F : Type*} [Field k] [IsAlgClosed k]
    [Field F] [Algebra k F] {ell : ℕ} (hell : ell.Prime)
    (x : PowerCompletion ell Fˣ) {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : x = 1 :=
  PowerCompletion.pow_eq_one hell (field_torsion_divisible (k := k) hell.pos) x hm hx

theorem completion_norm_inclusion {E F : Type*} [Field E] [Field F]
    [Algebra E F] {ell : ℕ} (x : PowerCompletion ell Eˣ) :
    PowerCompletion.map (normUnits E F) (PowerCompletion.map (inclusionUnits E F) x) =
      x ^ Module.finrank E F := by
  apply PowerCompletion.ext
  intro n
  change PowerClass.map (normUnits E F) _
    (PowerClass.map (inclusionUnits E F) _ (x.1 n)) = (x.1 n) ^ Module.finrank E F
  induction x.1 n using QuotientGroup.induction_on with
  | H u =>
    change PowerClass.map (normUnits E F) _
      (PowerClass.map (inclusionUnits E F) _ (PowerClass.mk (ell ^ n) u)) = _
    rw [PowerClass.map_mk, PowerClass.map_mk]
    change PowerClass.mk (ell ^ n) _ = (PowerClass.mk (ell ^ n) u) ^ Module.finrank E F
    rw [← map_pow]
    apply congrArg (PowerClass.mk (ell ^ n))
    ext
    exact Algebra.norm_algebraMap _

theorem finite_extension_completion_injective {k E F : Type*}
    [Field k] [IsAlgClosed k] [Field E] [Field F]
    [Algebra k E] [Algebra E F] [FiniteDimensional E F]
    {ell : ℕ} (hell : ell.Prime) :
    Function.Injective (PowerCompletion.map (ell := ell) (inclusionUnits E F)) := by
  apply (injective_iff_map_eq_one _).2
  intro x hx
  apply field_completion_pow_eq_one (k := k) hell x (Module.finrank_pos (R := E) (M := F))
  rw [← completion_norm_inclusion (F := F), hx, map_one]

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section
open scoped IntermediateField.algebraAdjoinAdjoin

theorem independent_powerClass_injective {E N ι : Type*} [Field E] [Field N]
    [Algebra E N] {x : ι → N} (hx : AlgebraicIndependent E x)
    (q : ℕ) (hq : 0 < q) :
    Function.Injective (PowerClass.map
      (inclusionUnits E (IntermediateField.adjoin E (Set.range x))) q) := by
  let R := Algebra.adjoin E (Set.range x)
  let F := IntermediateField.adjoin E (Set.range x)
  let : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv hx.aevalEquiv.toRingEquiv
  let f : R →ₐ[E] E := (MvPolynomial.aeval (fun _ : ι => (0 : E))).comp hx.repr
  apply (injective_iff_map_eq_one _).2
  intro z hz
  induction z using QuotientGroup.induction_on with
  | H u =>
    obtain ⟨v, hv⟩ := PowerClass.mk_eq_one.1 hz
    have hv' : (v : F) ^ q = algebraMap E F (u : E) := congrArg Units.val hv
    obtain ⟨a, ha⟩ : ∃ a : R, algebraMap R F a = (v : F) :=
      IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hq (by
        rw [hv', IsScalarTower.algebraMap_apply E R F]
        exact isIntegral_algebraMap)
    have hap : a ^ q = algebraMap E R (u : E) := by
      apply IsFractionRing.injective R F
      simpa only [map_pow, ha, ← IsScalarTower.algebraMap_apply E R F] using hv'
    have hfp : f a ^ q = (u : E) := by
      rw [← map_pow, hap, f.commutes]
      rfl
    have hf0 : f a ≠ 0 := by
      intro h
      exact u.ne_zero (by simpa [h, zero_pow hq.ne'] using hfp.symm)
    exact PowerClass.mk_eq_one.2 ⟨Units.mk0 (f a) hf0, Units.ext hfp⟩

theorem independent_completion_injective {E N ι : Type*} [Field E] [Field N]
    [Algebra E N] {x : ι → N} (hx : AlgebraicIndependent E x)
    {ell : ℕ} (hell : 0 < ell) :
    Function.Injective (PowerCompletion.map (ell := ell)
      (inclusionUnits E (IntermediateField.adjoin E (Set.range x)))) :=
  PowerCompletion.map_injective _ (fun n =>
    independent_powerClass_injective hx _ (pow_pos hell n))

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

theorem inclusionUnits_comp {E F N : Type*} [Field E] [Field F] [Field N]
    [Algebra E F] [Algebra F N] [Algebra E N] [IsScalarTower E F N] :
    (inclusionUnits F N).comp (inclusionUnits E F) = inclusionUnits E N := by
  ext u
  exact (IsScalarTower.algebraMap_apply E F N (u : E)).symm

theorem fg_extension_completion_injective {k E N : Type*}
    [Field k] [IsAlgClosed k] [Field E] [Field N]
    [Algebra k E] [Algebra k N] [Algebra E N] [IsScalarTower k E N]
    [Algebra.EssFiniteType E N] {ell : ℕ} (hell : ell.Prime) :
    Function.Injective (PowerCompletion.map (ell := ell) (inclusionUnits E N)) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis E N
  let F := IntermediateField.adjoin E (Set.range ((↑) : s → N))
  have : Algebra.EssFiniteType F N := Algebra.EssFiniteType.of_comp E F N
  have : Algebra.IsAlgebraic F N := hs.isAlgebraic_field
  have : Module.Finite F N := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have hp := independent_completion_injective hs.1 hell.pos
  have hf := finite_extension_completion_injective (k := k) (E := F) (F := N) hell
  have hc := hf.comp hp
  change Function.Injective ((PowerCompletion.map (ell := ell)
    (inclusionUnits F N)).comp (PowerCompletion.map (inclusionUnits E F))) at hc
  simpa only [← MonoidHom.coe_comp, PowerCompletion.map_comp, inclusionUnits_comp] using hc

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

lemma rational_variable_completion_ne_one (ell : ℕ) [Fact ell.Prime]
    (k : Type*) [Field k] :
    PowerCompletion.of (ell := ell) (Units.mk0 (RatFunc.X : RatFunc k) RatFunc.X_ne_zero) ≠ 1 := by
  intro h
  have h₁ := congrArg (fun z : PowerCompletion ell (RatFunc k)ˣ => z.val 1) h
  change PowerClass.mk (ell ^ 1) (Units.mk0 RatFunc.X RatFunc.X_ne_zero) = 1 at h₁
  rw [pow_one] at h₁
  obtain ⟨u, hu⟩ := PowerClass.mk_eq_one.mp h₁
  have hd := congrArg (rationalDegree k) hu
  rw [map_pow] at hd
  have hi := congrArg Multiplicative.toAdd hd
  change ell • RatFunc.intDegree (u : RatFunc k) =
    RatFunc.intDegree (RatFunc.X : RatFunc k) at hi
  have hd' : (ell : ℤ) * RatFunc.intDegree (u : RatFunc k) = 1 := by
    simpa only [nsmul_eq_mul, RatFunc.intDegree_X] using hi
  have hdvd : (ell : ℤ) ∣ 1 := ⟨_, hd'.symm⟩
  exact (Fact.out : ell.Prime).not_dvd_one (Int.natCast_dvd_natCast.mp hdvd)

lemma transcendental_completion_ne_one (ell : ℕ) [Fact ell.Prime]
    (k F : Type*) [Field k] [Field F] [IsAlgClosed k] [Algebra k F]
    [Algebra.EssFiniteType k F] (u : Fˣ) (hu : Transcendental k (u : F)) :
    PowerCompletion.of (ell := ell) u ≠ 1 := by
  let φ : RatFunc k →ₐ[k] F := RatFunc.liftAlgHom (Polynomial.aeval (u : F))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (transcendental_iff_injective.mp hu))
  let : Algebra (RatFunc k) F := φ.toRingHom.toAlgebra
  have : IsScalarTower k (RatFunc k) F :=
    IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
  have : Algebra.EssFiniteType (RatFunc k) F := Algebra.EssFiniteType.of_comp k _ F
  have hi := fg_extension_completion_injective (k := k) (E := RatFunc k) (N := F)
    (Fact.out : ell.Prime)
  have hx : φ RatFunc.X = (u : F) := by
    change RatFunc.liftRingHom _ _ (algebraMap (Polynomial k) (RatFunc k) Polynomial.X) = _
    erw [RatFunc.liftRingHom_algebraMap, Polynomial.aeval_X]
  have hx' : inclusionUnits (RatFunc k) F
      (Units.mk0 RatFunc.X RatFunc.X_ne_zero) = u := Units.ext hx
  intro h
  apply rational_variable_completion_ne_one ell k
  apply hi
  rw [map_one, PowerCompletion.map_of, hx', h]

theorem field_completion_kernel_constants
    (ell : ℕ) [Fact ell.Prime] (k F : Type*)
    [Field k] [Field F] [IsAlgClosed k] [Algebra k F]
    [Algebra.EssFiniteType k F] (u : Fˣ) :
    PowerCompletion.of (ell := ell) u = 1 ↔
      ∃ c : kˣ, inclusionUnits k F c = u := by
  constructor
  · intro h
    have ha : IsAlgebraic k (u : F) := by
      by_contra ht
      exact transcendental_completion_ne_one ell k F u ht h
    have he : algebraicClosure k F = ⊥ :=
      IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
    have hu' : (u : F) ∈ algebraicClosure k F := mem_algebraicClosure_iff.mpr ha
    rw [he] at hu'
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hu'
    have hc0 : c ≠ 0 := by
      intro h
      exact u.ne_zero (by simpa [h] using hc.symm)
    exact ⟨Units.mk0 c hc0, Units.ext hc⟩
  · rintro ⟨c, rfl⟩
    apply PowerCompletion.ext
    intro n
    change PowerClass.mk (ell ^ n) (inclusionUnits k F c) = 1
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (c : k)
      (pow_pos (Fact.out : ell.Prime).pos n)
    have hr0 : r ≠ 0 := by
      intro h
      exact c.ne_zero (by simpa [h, zero_pow (pow_pos (Fact.out : ell.Prime).pos n).ne'] using hr.symm)
    apply PowerClass.mk_eq_one.mpr
    exact ⟨inclusionUnits k F (Units.mk0 r hr0), Units.ext (by
      simp only [inclusionUnits, Units.val_pow_eq_pow_val, Units.coe_map,
        RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mk0, ← map_pow, hr])⟩

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

lemma integer_character_scalar (ell : ℕ) [Fact ell.Prime]
    {G : Type*} [CommGroup G] (d : G →* Multiplicative ℤ)
    {a : PadicInt ell} {x y : G} (h : KummerScalarLevels ell a x y) :
    (↑(Multiplicative.toAdd (d y)) : PadicInt ell) =
      a * (↑(Multiplicative.toAdd (d x)) : PadicInt ell) := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  have heq := h n
  rw [← map_pow, ← div_eq_one, ← map_div] at heq
  obtain ⟨z, hz⟩ := PowerClass.mk_eq_one.mp heq
  have hz' := congrArg d hz
  rw [map_pow, map_div, map_pow] at hz'
  have hi := congrArg Multiplicative.toAdd hz'
  have hi' : (ell ^ n : ℤ) * Multiplicative.toAdd (d z) =
      Multiplicative.toAdd (d y) - a.appr n * Multiplicative.toAdd (d x) := by
    simpa only [toAdd_pow, toAdd_div, nsmul_eq_mul, Nat.cast_pow] using hi
  have hzmod : (↑(Multiplicative.toAdd (d y)) : ZMod (ell ^ n)) =
      (a.appr n : ZMod (ell ^ n)) * (↑(Multiplicative.toAdd (d x)) : ZMod (ell ^ n)) := by
    apply sub_eq_zero.mp
    have hd : (ell ^ n : ℤ) ∣ Multiplicative.toAdd (d y) -
        a.appr n * Multiplicative.toAdd (d x) := ⟨_, hi'.symm⟩
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] using this
  simpa only [map_intCast, map_mul, PadicInt.toZModPow, PadicInt.toZModHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] using hzmod

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

lemma exponent_eq_of_zmod {G : Type*} [CommGroup G] (x : G) (q : ℕ)
    (hx : x ^ q = 1) {r s : ℤ} (hrs : (r : ZMod q) = (s : ZMod q)) :
    x ^ r = x ^ s := by
  have hd : (q : ℤ) ∣ r - s := (ZMod.intCast_zmod_eq_zero_iff_dvd (r - s) q).mp
    (by simpa using sub_eq_zero.mpr hrs)
  obtain ⟨t, ht⟩ := hd
  rw [← div_eq_one, div_eq_mul_inv, ← zpow_sub, ht, zpow_mul, zpow_natCast, hx, one_zpow]

theorem kummer_scalar_power_constants (ell : ℕ) [Fact ell.Prime]
    (k F : Type*) [Field k] [Field F] [IsAlgClosed k] [Algebra k F]
    [Algebra.EssFiniteType k F] {a : PadicInt ell} {x y : Fˣ}
    (h : KummerScalarLevels ell a x y) {r s : ℤ}
    (hrs : (r : PadicInt ell) = a * (s : PadicInt ell)) :
    ∃ c : kˣ, inclusionUnits k F c = y ^ s / x ^ r := by
  apply (field_completion_kernel_constants ell k F _).mp
  apply PowerCompletion.ext
  intro n
  change PowerClass.mk (ell ^ n) (y ^ s / x ^ r) = 1
  rw [map_div, map_zpow, map_zpow, h n]
  have he : (↑((a.appr n : ℤ) * s) : ZMod (ell ^ n)) = (r : ZMod (ell ^ n)) := by
    have hh := congrArg (PadicInt.toZModPow n) hrs.symm
    simpa only [map_mul, map_intCast, Int.cast_mul, Int.cast_natCast, PadicInt.toZModPow, PadicInt.toZModHom,
      RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] using hh
  rw [← zpow_natCast, ← zpow_mul, exponent_eq_of_zmod _ _ (PowerClass.pow_eq_one _ _) he,
    div_self']

end
end BogomolovPop

namespace BogomolovPop
noncomputable section

lemma cyclic_character_scalar_integer (ell : ℕ) [Fact ell.Prime]
    {G : Type*} [CommGroup G] (φ : G →* G) (d : G →* Multiplicative ℤ)
    {a : PadicInt ell} (hd : ∃ x, d x ≠ 1)
    (h : ∀ u, KummerScalarLevels ell a u (φ u)) : ∃ m : ℤ, a = m := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := d.range)
  obtain ⟨x, hx⟩ := g.property
  have hgne : (g : Multiplicative ℤ) ≠ 1 := by
    intro he
    obtain ⟨z, hz⟩ := hd
    obtain ⟨n, hn⟩ := hg ⟨d z, ⟨z, rfl⟩⟩
    have hh := congrArg (fun t : d.range => (t : Multiplicative ℤ)) hn
    simp only [Subgroup.coe_zpow, he, one_zpow] at hh
    exact hz hh.symm
  obtain ⟨m, hm⟩ := hg ⟨d (φ x), ⟨φ x, rfl⟩⟩
  have hm' := congrArg (fun t : d.range => Multiplicative.toAdd (t : Multiplicative ℤ)) hm
  have hm'' : m * Multiplicative.toAdd (d x) = Multiplicative.toAdd (d (φ x)) := by
    simpa only [Subgroup.coe_zpow, ← hx, toAdd_zpow, zsmul_eq_mul, Int.cast_id] using hm'
  have hc := integer_character_scalar ell d (h x)
  have hn : Multiplicative.toAdd (d x) ≠ 0 := by
    intro hh
    apply hgne
    rw [← hx]
    exact Multiplicative.toAdd.injective hh
  refine ⟨m, ?_⟩
  apply mul_right_cancel₀ (Int.cast_ne_zero.mpr hn : (↑(Multiplicative.toAdd (d x)) : PadicInt ell) ≠ 0)
  rw [← hc, ← hm'', Int.cast_mul]

theorem kummer_endomorphism_scalar_integer (ell : ℕ) [Fact ell.Prime]
    (k F : Type*) [Field k] [Field F] [Algebra k F]
    [Algebra.EssFiniteType k F] (φ : F →+* F) {a : PadicInt ell}
    (hx : ∃ x : Fˣ, Transcendental k (x : F))
    (h : ∀ u : Fˣ, KummerScalarLevels ell a u (Units.map φ.toMonoidHom u)) :
    ∃ m : ℤ, a = m := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨d, hd⟩ := transcendental_integer_character k F x hx
  exact cyclic_character_scalar_integer ell (Units.map φ.toMonoidHom) d ⟨x, hd⟩ h

end
end BogomolovPop
noncomputable section
namespace BogomolovPop

open Polynomial

lemma transcendental_ne_zero {k F : Type*} [Field k] [Field F] [Algebra k F]
    {x : F} (hx : Transcendental k x) : x ≠ 0 := by
  rintro rfl
  exact hx isAlgebraic_zero

lemma transcendental_add_constant {k F : Type*} [Field k] [Field F] [Algebra k F]
    {x : F} (hx : Transcendental k x) (c : k) :
    Transcendental k (x + algebraMap k F c) := by
  intro h
  apply hx
  simpa using h.sub (isIntegral_algebraMap (x := c)).isAlgebraic

lemma integer_power_shift_nonneg {k F : Type*} [Field k] [Field F] [Algebra k F]
    {x : F} (hx : Transcendental k x) (a b : k) (ha : a ≠ 0) {m : ℤ}
    (h : algebraMap k F a * x ^ m + 1 = algebraMap k F b * (x + 1) ^ m) :
    0 ≤ m := by
  have hx0 := transcendental_ne_zero hx
  have hx1 : x + 1 ≠ 0 := by
    simpa using transcendental_ne_zero (transcendental_add_constant hx (1 : k))
  cases m with
  | ofNat n => exact Int.natCast_nonneg _
  | negSucc n =>
    simp only [zpow_negSucc] at h
    have he : algebraMap k F a * (x + 1) ^ (n + 1) +
        x ^ (n + 1) * (x + 1) ^ (n + 1) = algebraMap k F b * x ^ (n + 1) := by
      field_simp [hx0, hx1] at h
      linear_combination h
    have hp : C a * (X + 1) ^ (n + 1) + X ^ (n + 1) * (X + 1) ^ (n + 1) =
        C b * X ^ (n + 1) := by
      apply (transcendental_iff_injective.mp hx)
      simpa using he
    have hc := congrArg (Polynomial.eval (0 : k)) hp
    simp at hc
    exact (ha hc).elim

lemma positive_power_shift {k F : Type*} [Field k] [Field F] [Algebra k F]
    {x : F} (hx : Transcendental k x) (a b : k) {n : ℕ} (hn : 0 < n)
    (h : algebraMap k F a * x ^ n + 1 = algebraMap k F b * (x + 1) ^ n) :
    a = 1 ∧ b = 1 ∧ (X + 1 : k[X]) ^ n = X ^ n + 1 := by
  have hp : C a * X ^ n + 1 = C b * (X + 1 : k[X]) ^ n := by
    apply transcendental_iff_injective.mp hx
    simpa using h
  have hb := congrArg (Polynomial.eval (0 : k)) hp
  simp [Nat.ne_of_gt hn] at hb
  have ha := congrArg (fun p : k[X] => p.coeff n) hp
  simp [Nat.ne_of_gt hn, coeff_X_add_one_pow, coeff_one] at ha
  have ha1 : a = 1 := ha.trans hb.symm
  refine ⟨ha1, hb.symm, ?_⟩
  simpa [ha1, hb.symm] using hp.symm

lemma power_relation_shift {k F : Type*} [Field k] [Field F] [Algebra k F]
    (φ : F →+* F) {m : ℤ} (h : IntegerPowerModuloConstants k F φ m)
    {x : F} (hx : Transcendental k x) :
    ∃ a b : kˣ, φ x = algebraMap k F (a : k) * x ^ m ∧
      algebraMap k F (a : k) * x ^ m + 1 =
        algebraMap k F (b : k) * (x + 1) ^ m := by
  obtain ⟨a, ha⟩ := h (Units.mk0 x (transcendental_ne_zero hx))
  have hx1 : x + 1 ≠ 0 := by
    simpa using transcendental_ne_zero (transcendental_add_constant hx (1 : k))
  obtain ⟨b, hb⟩ := h (Units.mk0 (x + 1) hx1)
  simp only [Units.val_mk0] at ha hb
  refine ⟨a, b, ha, ?_⟩
  simpa only [Units.val_mk0, map_add, map_one, ha] using hb

lemma power_endomorphism_transcendental {k F : Type*} [Field k] [Field F] [Algebra k F]
    (φ : F →+* F) {n : ℕ} (hn : 0 < n)
    (h : IntegerPowerModuloConstants k F φ (n : ℤ))
    {x : F} (hx : Transcendental k x) :
    φ x = x ^ n ∧ (X + 1 : k[X]) ^ n = X ^ n + 1 := by
  obtain ⟨a, b, ha, hab⟩ := power_relation_shift φ h hx
  simp only [zpow_natCast] at ha hab
  obtain ⟨ha1, _, hp⟩ := positive_power_shift hx (a : k) (b : k) hn hab
  exact ⟨by simpa [ha1] using ha, hp⟩

lemma polynomial_power_prime (k F : Type*) [Field k] [Field F] [Algebra k F]
    {n : ℕ} (hn : 0 < n) (hp : (X + 1 : k[X]) ^ n = X ^ n + 1) :
    n = 1 ∨ ∃ p r : ℕ, p.Prime ∧ (p : F) = 0 ∧ n = p ^ r := by
  have hcoeff : ∀ i, 0 < i → i < n → (n.choose i : k) = 0 := by
    intro i hi hin
    have he := congrArg (fun q : k[X] => q.coeff i) hp
    simpa [coeff_X_add_one_pow, coeff_X_pow, coeff_one, Nat.ne_of_gt hi,
      Nat.ne_of_lt hin] using he
  obtain ⟨p, hchar⟩ := CharP.exists k
  let := hchar
  rcases CharP.char_is_prime_or_zero k p with hprime | rfl
  · let : Fact p.Prime := ⟨hprime⟩
    right
    refine ⟨p, multiplicity p n, hprime, ?_, ?_⟩
    · have hc : (p : k) = 0 := (CharP.cast_eq_zero_iff k p p).mpr dvd_rfl
      simpa only [map_natCast, map_zero] using congrArg (algebraMap k F) hc
    · apply Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat hn
      intro i hi
      apply Nat.modEq_zero_iff_dvd.mpr
      apply (CharP.cast_eq_zero_iff k p _).mp
      exact hcoeff i (by have := (Finset.mem_Icc.mp hi).1; omega)
        (by have := (Finset.mem_Icc.mp hi).2; omega)
  · left
    by_contra hne
    have hc := hcoeff 1 (by omega) (by omega)
    simp only [Nat.choose_one_right] at hc
    have : 0 ∣ n := (CharP.cast_eq_zero_iff k 0 n).mp hc
    exact (Nat.ne_of_gt hn) (zero_dvd_iff.mp this)

lemma algebraic_is_constant {k F : Type*} [Field k] [Field F] [Algebra k F]
    [IsAlgClosed k] {x : F} (hx : IsAlgebraic k x) : ∃ c : k, algebraMap k F c = x := by
  have he : algebraicClosure k F = ⊥ :=
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  have hx' : x ∈ algebraicClosure k F := mem_algebraicClosure_iff.mpr hx
  rw [he] at hx'
  exact IntermediateField.mem_bot.mp hx'

lemma power_endomorphism_constants {k F : Type*} [Field k] [Field F] [Algebra k F]
    (φ : F →+* F) {n : ℕ} (hn : 0 < n)
    (h : IntegerPowerModuloConstants k F φ (n : ℤ))
    {t : F} (ht : Transcendental k t) (c : k) :
    φ (algebraMap k F c) = (algebraMap k F c) ^ n := by
  by_cases hc : c = 0
  · simp [hc, Nat.ne_of_gt hn]
  obtain ⟨d, hd⟩ := h (Units.map (algebraMap k F).toMonoidHom (Units.mk0 c hc))
  have hd' : φ (algebraMap k F c) = algebraMap k F ((d : k) * c ^ n) := by
    simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Units.val_mk0, zpow_natCast, map_mul, map_pow] using hd
  have ht' := (power_endomorphism_transcendental φ hn h ht).1
  have hc' := (power_endomorphism_transcendental φ hn h
    (transcendental_add_constant ht c)).1
  have hp : (X + C c : k[X]) ^ n = X ^ n + C ((d : k) * c ^ n) := by
    apply transcendental_iff_injective.mp ht
    simpa only [map_pow, map_add, aeval_X, aeval_C, ← ht', ← hd'] using hc'.symm
  have hz := congrArg (Polynomial.eval (0 : k)) hp
  simp only [eval_pow, eval_add, eval_X, eval_C, zero_add, zero_pow (Nat.ne_of_gt hn)] at hz
  rw [hd', ← hz, map_pow]

 theorem integer_power_endomorphism_rigid
    (k F : Type*) [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    (φ : F →+* F) {m : ℤ} (hm : m ≠ 0)
    (ht : ∃ x : F, Transcendental k x)
    (h : IntegerPowerModuloConstants k F φ m) :
    ∃ n : ℕ, m = n ∧ (∀ x : F, φ x = x ^ n) ∧
      (n = 1 ∨ ∃ p r : ℕ, p.Prime ∧ (p : F) = 0 ∧ n = p ^ r) := by
  obtain ⟨t, ht⟩ := ht
  obtain ⟨a, b, _, hab⟩ := power_relation_shift φ h ht
  have hmpos : 0 ≤ m := integer_power_shift_nonneg ht (a : k) (b : k) a.ne_zero hab
  lift m to ℕ using hmpos with n
  have hn : 0 < n := by omega
  refine ⟨n, rfl, ?_, polynomial_power_prime k F hn
    (power_endomorphism_transcendental φ hn h ht).2⟩
  intro x
  by_cases hx : IsAlgebraic k x
  · obtain ⟨c, rfl⟩ := algebraic_is_constant hx
    exact power_endomorphism_constants φ hn h ht c
  · exact (power_endomorphism_transcendental φ hn h hx).1

end BogomolovPop

namespace BogomolovPop
noncomputable section

theorem kummer_endomorphism_frobenius (ell : ℕ) [Fact ell.Prime]
    (k F : Type*) [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    [Algebra.EssFiniteType k F] (φ : F →+* F) (a : (PadicInt ell)ˣ)
    (hx : ∃ x : F, Transcendental k x)
    (h : ∀ u : Fˣ, KummerScalarLevels ell (a : PadicInt ell) u
      (Units.map φ.toMonoidHom u)) :
    φ = RingHom.id F ∨ ∃ p r : ℕ, p.Prime ∧ (p : F) = 0 ∧
      ∀ x : F, φ x = x ^ (p ^ r) := by
  obtain ⟨m, hm⟩ := kummer_endomorphism_scalar_integer ell k F φ
    (by obtain ⟨x, hx⟩ := hx; exact ⟨Units.mk0 x (transcendental_ne_zero hx), hx⟩) h
  have hm0 : m ≠ 0 := by
    intro hh
    apply a.ne_zero
    simpa only [hh, Int.cast_zero] using hm
  have hp : IntegerPowerModuloConstants k F φ m := by
    intro u
    obtain ⟨c, hc⟩ := kummer_scalar_power_constants ell k F (h u)
      (r := m) (s := 1) (by simpa using hm.symm)
    have he := congrArg Units.val hc
    simp only [inclusionUnits, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, Units.val_div_eq_div_val, zpow_one, Units.val_zpow_eq_zpow_val] at he
    exact ⟨c, (eq_div_iff (zpow_ne_zero _ u.ne_zero)).mp he |>.symm⟩
  obtain ⟨n, _, hφ, hn⟩ := integer_power_endomorphism_rigid k F φ hm0 hx hp
  rcases hn with rfl | ⟨p, r, hprime, hchar, rfl⟩
  · left
    ext x
    simpa using hφ x
  · exact Or.inr ⟨p, r, hprime, hchar, hφ⟩

end
end BogomolovPop

end
end
end

end OAI

-- ---- platform node ----
open OAI OAI.BogomolovPop
open scoped Topology

theorem solution (ell : ℕ) [Fact ell.Prime]
    (k F : Type*) [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    [Algebra.EssFiniteType k F] (φ : F →+* F) (a : (PadicInt ell)ˣ)
    (hx : ∃ x : F, Transcendental k x)
    (h : ∀ u : Fˣ, KummerScalarLevels ell (a : PadicInt ell) u
      (Units.map φ.toMonoidHom u)) :
    φ = RingHom.id F ∨ ∃ p r : ℕ, p.Prime ∧ (p : F) = 0 ∧
      ∀ x : F, φ x = x ^ (p ^ r) := by
  first
    | exact OAI.BogomolovPop.kummer_endomorphism_frobenius ell k F φ a hx h
    | exact OAI.BogomolovPop.kummer_endomorphism_frobenius
    | (apply OAI.BogomolovPop.kummer_endomorphism_frobenius <;> assumption)
    | (intros; apply OAI.BogomolovPop.kummer_endomorphism_frobenius <;> assumption)
