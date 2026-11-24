-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.card_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:30:29.919913+00:00
-- url     : https://prove2.me/submissions/33e7cfc5-2ce5-4d1c-94b4-acb18cd21fa2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj
import Theorems.Thm_GlobalTheory_HeckeCompare_card_orth_mul
import Theorems.Thm_GlobalTheory_HeckeCompare_ev_pow
import Theorems.Thm_GlobalTheory_HeckeCompare_triv_iff
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [CommGroup Q] {ρ : 𝓞 E → Q →* Q} {e : ℕ → Q → Q → kˣ → Prop}
  (I : TateIso D k Q (fun a x => ρ a x) e)
variable (hu : Uniq e)
include hu
include I
namespace GlobalTheory.HeckeCompare
theorem _root_.solution [IsAlgClosed k] [CharZero k] {p : ℕ} (hp : 0 < p) (hf : Finite {x : Q // x ^ p = 1})
    (S : Subgroup Q) (hS : ∀ c ∈ S, c ^ p = 1) :
    Nat.card {x : Q // x ^ p = 1 ∧ ∀ c ∈ S, e p x c 1} * Nat.card S = Nat.card {x : Q // x ^ p = 1} := by
  let G : Subgroup Q := (powMonoidHom p).ker
  have : Finite G := hf
  have hs : ∀ x : G, ∃ a, I.ev p a = x := fun x => (I.onto p hp _).1 x.2
  choose s hs using hs
  have hv : ∀ (x y : G) a b, I.ev p a = x → I.ev p b = y → I.ζ p ^ D.EF (s x) (s y) = I.ζ p ^ D.EF a b :=
    fun x y a b ha hb => hu p x y _ _ hp x.2 y.2 (by simpa only [hs] using I.isom p hp (s x) (s y))
      (by simpa only [ha, hb] using I.isom p hp a b)
  let B : G →* G →* kˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (fun y => I.ζ p ^ D.EF (s x) (s y)) fun y y' => by
      rw [hv x (y * y') (s x) (s y + s y') (hs x) (by rw [I.add, hs, hs]; rfl), map_add, zpow_add])
    fun x x' => MonoidHom.ext fun y => by
      show I.ζ p ^ D.EF (s (x * x')) (s y) = I.ζ p ^ D.EF (s x) (s y) * I.ζ p ^ D.EF (s x') (s y)
      rw [hv (x * x') y (s x + s x') (s y) (by rw [I.add, hs, hs]; rfl) (hs y), map_add, LinearMap.add_apply, zpow_add]
  have hB1 : ∀ x y : G, B x y = 1 ↔ e p x y 1 := fun x y => by
    rw [← hs x, ← hs y, triv_iff I hu hp, ← (I.ζ_prim p hp).zpow_eq_one_iff_dvd]
    rfl
  have hB : Function.Injective B := (injective_iff_map_eq_one B).2 fun x hx => by
    have h₁ : ∀ b, (p : ℤ) ∣ D.EF (s x) b := fun b => by
      rw [← triv_iff I hu hp, hs]
      exact (hB1 x ⟨_, ev_pow I hp b⟩).1 (by rw [hx]; rfl)
    choose f hf using h₁
    have hp' : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
    obtain ⟨a, ha⟩ := D.unimod.2 (AddMonoidHom.mk' f fun b b' => mul_left_cancel₀ hp' (by
      rw [mul_add, ← hf, ← hf, ← hf, map_add])).toIntLinearMap
    refine Subtype.ext ((hs x).symm.trans ((I.ker p hp _).2 ⟨a, D.unimod.1 (LinearMap.ext fun b => ?_)⟩))
    rw [map_nsmul, LinearMap.smul_apply, ha, hf, nsmul_eq_mul]
    rfl
  have h := card_orth_mul B hB (S.subgroupOf G)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show S ≤ G from hS)).toEquiv] at h
  refine Eq.trans (congrArg (· * _) (Nat.card_congr ?_)) h
  exact ⟨fun x => ⟨⟨x.1, x.2.1⟩, fun c hc => (hB1 _ _).2 (x.2.2 c.1 hc)⟩,
    fun x => ⟨x.1.1, x.1.2, fun c hc => (hB1 x.1 ⟨c, hS c hc⟩).1 (x.2 _ hc)⟩, fun _ => rfl, fun _ => rfl⟩
end GlobalTheory.HeckeCompare
