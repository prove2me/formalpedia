-- Prove2me | solution 1 for GlobalTheory.GramCount.primitive_gram_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:40:17.841777+00:00
-- url     : https://prove2.me/submissions/6dea884e-fe2c-4078-ba3a-bb2418b8dfbb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesWithGramMatrixHenselCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesGramModNilpotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesWithGramMatrixResidueRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizer
import Theorems.Thm_GlobalTheory_GramCount_quotInv_mk
import Theorems.Thm_GlobalTheory_GramCount_count_quot
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_GramCount_Prim_map
import Theorems.Thm_GlobalTheory_GramCount_map_ip
import Theorems.Thm_GlobalTheory_GramCount_prim_of_map
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_int_of_fixed
import Theorems.Thm_GlobalTheory_UnramOrder_exists_sub_cj_mul_eq_one
import Theorems.Thm_GlobalTheory_UnramOrder_order_facts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.GramCount
namespace GlobalTheory.GramCount
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (n m j : ℕ), 2 * m + 3 ≤ n → 1 ≤ j → ∀ (Gm : Matrix (Fin m) (Fin m) E), IsHerm L Gm → IsIntM L Gm → ∀ (R : Finset E), (∀ u ∈ R, u ∈ L.O) → (∀ u ∈ L.O, ∃! w, w ∈ R ∧ ∃ c ∈ L.O, u - w = algebraMap F E ((ϖ : F) ^ j) * c) → ∀ N : ℕ, N = Set.ncard {x : Fin m → Fin n → E | (∀ a i, x a i ∈ R) ∧ (∃ y : Fin m → Fin n → E, (∀ a i, y a i ∈ L.O) ∧ ∀ a b, hf L 1 (x a) (y b) = if a = b then 1 else 0) ∧ ∀ a b, ∃ c ∈ L.O, hf L 1 (x b) (x a) - Gm a b = algebraMap F E ((ϖ : F) ^ j) * c} → (resQ ϖ : ℝ) ^ (j * (2 * n * m - m ^ 2)) ≤ 2 * N ∧ (N : ℝ) ≤ 2 * (resQ ϖ : ℝ) ^ (j * (2 * n * m - m ^ 2)) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n m j hmn hj Gm hHm hIm R hR hrep N hN
  classical
  obtain ⟨-, -, -, -, hmemF, hcardj, hq2, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ

  let c : L.O →+* L.O :=
    (L.cj : E →+* E).restrict L.O L.O (fun x hx => GlobalTheory.UnramOrder.cj_mem L hx)
  have hcv : ∀ u : L.O, (c u : E) = L.cj u := fun u => rfl
  have hc : ∀ u, c (c u) = u := fun u => Subtype.ext (L.cj_cj u)
  obtain ⟨ω0, hω0, e0, he0, hωe⟩ := GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  have hω : IsUnit ((⟨ω0, hω0⟩ : L.O) - c ⟨ω0, hω0⟩) :=
    IsUnit.of_mul_eq_one (⟨e0, he0⟩ : L.O) (Subtype.ext hωe)

  let p : L.O := ⟨algebraMap F E (ϖ : F), (hmemF _).2 ϖ.2⟩
  have hpv : ∀ k : ℕ, ((p ^ k : L.O) : E) = algebraMap F E ((ϖ : F) ^ k) := by
    intro k
    rw [SubmonoidClass.coe_pow, map_pow]
  have hp : c p = p := Subtype.ext (L.cj.commutes _)
  have hpj : c (p ^ j) = p ^ j := by rw [map_pow, hp]
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hpnu : ¬ IsUnit p := by
    intro hu
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hv1 : algebraMap F E (ϖ : F) * v = 1 := congrArg Subtype.val hv
    have hv2 : algebraMap F E (ϖ : F)⁻¹ * algebraMap F E (ϖ : F) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hϖ0, map_one]
    have hvE : (v : E) = algebraMap F E (ϖ : F)⁻¹ := by
      calc (v : E) = algebraMap F E (ϖ : F)⁻¹ * (algebraMap F E (ϖ : F) * v) := by
            rw [← mul_assoc, hv2, one_mul]
        _ = algebraMap F E (ϖ : F)⁻¹ := by rw [hv1, mul_one]
    have hmem : (ϖ : F)⁻¹ ∈ 𝒪[F] := by
      rw [← hmemF, ← hvE]
      exact v.2
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one (a := ϖ) (⟨_, hmem⟩ : 𝒪[F]) (Subtype.ext (mul_inv_cancel₀ hϖ0)))

  have hK : ∀ t : L.O, c t = t → ¬ p ∣ t → IsUnit t := by
    intro t ht hnd
    obtain ⟨a, ha⟩ := GlobalTheory.UnramOrder.exists_int_of_fixed L t.2 (congrArg Subtype.val ht)
    have hau : IsUnit a := by
      by_contra hna
      have hmax : a ∈ IsLocalRing.maximalIdeal 𝒪[F] :=
        (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hna)
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
        Ideal.mem_span_singleton] at hmax
      obtain ⟨b, rfl⟩ := hmax
      exact hnd ⟨⟨algebraMap F E (b : F), (hmemF _).2 b.2⟩,
        Subtype.ext (ha.trans (map_mul (algebraMap F E) (ϖ : F) (b : F)))⟩
    obtain ⟨u, rfl⟩ := hau
    have huw : ((u : 𝒪[F]) : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = 1 :=
      congrArg Subtype.val u.mul_inv
    refine IsUnit.of_mul_eq_one (a := t) (M := L.O) ⟨algebraMap F E (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F),
      (hmemF _).2 ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]).2⟩ (Subtype.ext ?_)
    show (t : E) * algebraMap F E (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) = 1
    rw [ha, ← map_mul, huw, map_one]

  have hjac : ∀ u : L.O, u ∈ Ideal.span {p ^ j} → IsUnit (1 + u) := by
    intro u hu
    rw [Ideal.mem_span_singleton] at hu
    obtain ⟨v, rfl⟩ := hu
    have hfix : c ((1 + p ^ j * v) * c (1 + p ^ j * v)) = (1 + p ^ j * v) * c (1 + p ^ j * v) := by
      rw [map_mul, hc, mul_comm]
    have hcv' : c (1 + p ^ j * v) = 1 + p ^ j * c v := by
      rw [map_add, map_one, map_mul, map_pow, hp]
    have hnd : ¬ p ∣ (1 + p ^ j * v) * c (1 + p ^ j * v) := by
      rintro ⟨s, hs⟩
      rw [hcv'] at hs
      have hpj' : p ^ j = p * p ^ (j - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      apply hpnu
      refine IsUnit.of_mul_eq_one (a := p) (s - p ^ (j - 1) * (v + c v + p ^ j * v * c v)) ?_
      linear_combination (-1 : L.O) * hs + (v + c v + p ^ j * v * c v) * hpj'
    exact isUnit_of_mul_isUnit_left (hK _ hfix hnd)

  have hsetj : ∀ k : ℕ, {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ k)} = {p ^ k} := by
    intro k
    ext y
    rw [Set.mem_ofPred_eq, Set.mem_singleton_iff, ← hpv k]
    exact ⟨fun h => Subtype.ext h, fun h => h ▸ rfl⟩
  have h2 : Nat.card (L.O ⧸ Ideal.span {p ^ j}) = resQ ϖ ^ (2 * j) := by
    have := hcardj j
    rwa [hsetj j] at this
  have h1 : Nat.card (L.O ⧸ Ideal.span {p}) = resQ ϖ ^ 2 := by
    have := hcardj 1
    rwa [hsetj 1, pow_one, mul_one] at this
  have hmkeq : ∀ u v : L.O, Ideal.Quotient.mk (Ideal.span {p ^ j}) u = Ideal.Quotient.mk _ v ↔
      ∃ c0 ∈ L.O, (u : E) - v = algebraMap F E ((ϖ : F) ^ j) * c0 := by
    intro u v
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, k.2, ?_⟩
      rw [← hpv j]
      exact congrArg Subtype.val hk
    · rintro ⟨c0, hc0, h⟩
      refine ⟨⟨c0, hc0⟩, Subtype.ext ?_⟩
      rw [← hpv j] at h
      exact h

  have hrepQ : ∀ z : L.O ⧸ Ideal.span {p ^ j}, ∃ w : E, ∃ hw : w ∈ L.O,
      w ∈ R ∧ Ideal.Quotient.mk _ (⟨w, hw⟩ : L.O) = z := by
    intro z
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨w, ⟨hwR, c0, hc0, hw⟩, -⟩ := hrep u u.2
    refine ⟨w, hR w hwR, hwR, (hmkeq _ _).2 ⟨-c0, neg_mem hc0, ?_⟩⟩
    show w - (u : E) = _
    rw [mul_neg, ← hw]
    ring
  choose rp hrpO hrpR hrpmk using hrepQ
  have hrp_eq : ∀ w (hw : w ∈ R),
      rp (Ideal.Quotient.mk (Ideal.span {p ^ j}) (⟨w, hR w hw⟩ : L.O)) = w := by
    intro w hw
    obtain ⟨c0, hc0, hc⟩ := (hmkeq _ _).1 (hrpmk (Ideal.Quotient.mk (Ideal.span {p ^ j})
      (⟨w, hR w hw⟩ : L.O)))
    have hc' : rp (Ideal.Quotient.mk (Ideal.span {p ^ j}) (⟨w, hR w hw⟩ : L.O)) - w =
        algebraMap F E ((ϖ : F) ^ j) * c0 := hc
    obtain ⟨w', -, huniq⟩ := hrep w (hR w hw)
    have ea := huniq _ ⟨hrpR _, -c0, neg_mem hc0, by rw [mul_neg, ← hc']; ring⟩
    have eb := huniq w ⟨hw, 0, zero_mem _, by rw [sub_self, mul_zero]⟩
    exact ea.trans eb.symm

  have hfv : ∀ u v : Fin n → L.O,
      hf L 1 (fun i => (u i : E)) (fun i => (v i : E)) = ((ip c u v : L.O) : E) := by
    intro u v
    simp [hf, ip, Matrix.one_apply, hcv]
  let cA := quotInv c (p ^ j) hpj
  have hφc' : ∀ u, Ideal.Quotient.mk (Ideal.span {p ^ j}) (c u) = cA (Ideal.Quotient.mk _ u) :=
    fun u => (quotInv_mk c (p ^ j) hpj u).symm
  have hk : ∀ u, Ideal.Quotient.mk (Ideal.span {p ^ j}) u = 0 → IsUnit (1 + u) :=
    fun u hu => hjac u (Ideal.Quotient.eq_zero_iff_mem.1 hu)
  have hEprim : ∀ u : Fin m → Fin n → L.O,
      (∃ y : Fin m → Fin n → E, (∀ a i, y a i ∈ L.O) ∧
        ∀ a b, hf L 1 (fun i => (u a i : E)) (y b) = if a = b then 1 else 0) ↔ Prim c u := by
    intro u
    constructor
    · rintro ⟨y, hyO, hy⟩
      refine ⟨fun b i => ⟨y b i, hyO b i⟩, fun a b => Subtype.ext ?_⟩
      have e : hf L 1 (fun i => (u a i : E)) (fun i => ((⟨y b i, hyO b i⟩ : L.O) : E)) =
          if a = b then 1 else 0 := hy a b
      rw [hfv] at e
      exact e.trans (by split_ifs <;> rfl)
    · rintro ⟨y, hy⟩
      refine ⟨fun b i => (y b i : E), fun b i => (y b i).2, fun a b => ?_⟩
      have e := congrArg Subtype.val (hy a b)
      rw [← hfv] at e
      exact e.trans (by split_ifs <;> rfl)
  let GO : Matrix (Fin m) (Fin m) L.O := fun a b => ⟨Gm a b, hIm a b⟩
  have hGO : ∀ a b, c (GO b a) = GO a b := fun a b => Subtype.ext (congrFun (congrFun hHm a) b)
  have hgram : ∀ u : Fin m → Fin n → L.O,
      (∀ a b, ∃ c0 ∈ L.O, hf L 1 (fun i => (u b i : E)) (fun i => (u a i : E)) - Gm a b =
        algebraMap F E ((ϖ : F) ^ j) * c0) ↔
      ∀ a b, ip cA (fun i => Ideal.Quotient.mk (Ideal.span {p ^ j}) (u b i))
        (fun i => Ideal.Quotient.mk (Ideal.span {p ^ j}) (u a i)) =
          Ideal.Quotient.mk (Ideal.span {p ^ j}) (GO a b) := by
    intro u
    refine forall_congr' fun a => forall_congr' fun b => ?_
    rw [← map_ip c cA _ hφc', hmkeq, hfv]

  have hset : {x : Fin m → Fin n → E | (∀ a i, x a i ∈ R) ∧ (∃ y : Fin m → Fin n → E,
      (∀ a i, y a i ∈ L.O) ∧ ∀ a b, hf L 1 (x a) (y b) = if a = b then 1 else 0) ∧
      ∀ a b, ∃ c ∈ L.O, hf L 1 (x b) (x a) - Gm a b = algebraMap F E ((ϖ : F) ^ j) * c} =
      (fun z a i => rp (z a i)) '' sols cA n (GO.map (Ideal.Quotient.mk _)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hx, hprim, hgr⟩
      let u : Fin m → Fin n → L.O := fun a i => ⟨x a i, hR _ (hx a i)⟩
      refine ⟨fun a i => Ideal.Quotient.mk _ (u a i), And.intro ?_ ?_, ?_⟩
      · exact Prim.map c cA _ hφc' ((hEprim u).1 hprim)
      · exact (hgram u).1 hgr
      · funext a i
        exact hrp_eq (x a i) (hx a i)
    · rintro ⟨z, ⟨hzp, hzg⟩, rfl⟩
      let u : Fin m → Fin n → L.O := fun a i => ⟨rp (z a i), hrpO (z a i)⟩
      have hu : (fun a i => Ideal.Quotient.mk (Ideal.span {p ^ j}) (u a i)) = z :=
        funext fun a => funext fun i => hrpmk (z a i)
      refine ⟨fun a i => hrpR (z a i), (hEprim u).2 ?_, (hgram u).2 ?_⟩
      · apply prim_of_map c hc cA _ hφc' Ideal.Quotient.mk_surjective hk
        rw [hu]
        exact hzp
      · intro a b
        have e := hzg a b
        rw [← hu] at e
        exact e
  have hinj : Function.Injective
      (fun (z : Fin m → Fin n → L.O ⧸ Ideal.span {p ^ j}) (a : Fin m) (i : Fin n) => rp (z a i)) := by
    intro z z' h
    funext a i
    have e : rp (z a i) = rp (z' a i) := congrFun (congrFun h a) i
    calc z a i = Ideal.Quotient.mk _ ⟨rp (z a i), hrpO _⟩ := (hrpmk _).symm
      _ = Ideal.Quotient.mk _ ⟨rp (z' a i), hrpO _⟩ := congrArg _ (Subtype.ext e)
      _ = z' a i := hrpmk _
  have hN' : N = Set.ncard (sols cA n (GO.map (Ideal.Quotient.mk _))) :=
    hN.trans ((congrArg Set.ncard hset).trans (Set.ncard_image_of_injective _ hinj))
  exact count_quot c hc _ hω p hp hK (resQ ϖ) hq2 j hj h1 h2 hpj m n hmn GO hGO N hN'
end GlobalTheory.GramCount
