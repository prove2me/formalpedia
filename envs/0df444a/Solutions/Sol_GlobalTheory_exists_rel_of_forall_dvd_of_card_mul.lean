-- Prove2me | solution 1 for GlobalTheory.exists_rel_of_forall_dvd_of_card_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:37:48.780961+00:00
-- url     : https://prove2.me/submissions/b086e247-3cec-4cfc-9a4c-84f4113ca9a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEqNsmulOfForallDvdOfBijective
import Theorems.Thm_GlobalTheory_exists_eq_nsmul_of_forall_dvd_of_bijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace GlobalTheory
private theorem card_mul_card_orthogonal_eq_card_of_nondegenerate {Q : Type} [AddCommGroup Q] [Finite Q] (N : ℕ)
    [NeZero N] (B : Q →+ Q →+ ZMod N) (hL : ∀ y, (∀ x, B y x = 0) → y = 0)
    (U : AddSubgroup Q) :
    Nat.card U * Nat.card (⨅ t ∈ U, (B t).ker : AddSubgroup Q) = Nat.card Q := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  set V : AddSubgroup Q := ⨅ t ∈ U, (B t).ker with hV
  have hmemV : ∀ x, x ∈ V ↔ ∀ t ∈ U, B t x = 0 := by
    intro x; simp [hV, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker]
  let e : AddChar (ZMod N) ℂ := ZMod.stdAddChar
  have he : ∀ z, e z = 1 → z = 0 := by
    intro z h
    apply ZMod.injective_stdAddChar
    change e z = e 0
    rw [h, AddChar.map_zero_eq_one]
  have hrow : ∀ t : U, ∑ x : Q, e (B t x) = if t = 0 then (Fintype.card Q : ℂ) else 0 := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp
    · rw [if_neg ht]
      have hne : e.compAddMonoidHom (B t) ≠ 0 := by
        intro h
        apply ht
        have h0 : (t : Q) = 0 := by
          apply hL
          intro x
          apply he
          have := DFunLike.congr_fun h x
          simpa using this
        exact Subtype.ext h0
      exact AddChar.sum_eq_zero_iff_ne_zero.mpr hne
  have hcol : ∀ x : Q, ∑ t : U, e (B t x) = if x ∈ V then (Fintype.card U : ℂ) else 0 := by
    intro x
    by_cases hx : x ∈ V
    · rw [if_pos hx]
      have : ∀ t : U, e (B t x) = 1 := by
        intro t
        rw [(hmemV x).mp hx t t.2, AddChar.map_zero_eq_one]
      simp [this]
    · rw [if_neg hx]
      have hne : e.compAddMonoidHom ((B.flip x).comp U.subtype) ≠ 0 := by
        intro h
        apply hx
        rw [hmemV]
        intro t ht
        apply he
        have := DFunLike.congr_fun h ⟨t, ht⟩
        simpa using this
      have := AddChar.sum_eq_zero_iff_ne_zero.mpr hne
      simpa using this
  have hA : ∑ t : U, ∑ x : Q, e (B t x) = (Fintype.card Q : ℂ) := by
    rw [Fintype.sum_eq_single 0 (fun t ht => by rw [hrow t, if_neg ht])]
    rw [hrow 0, if_pos rfl]
  have hB : ∑ t : U, ∑ x : Q, e (B t x) = (Fintype.card V : ℂ) * (Fintype.card U : ℂ) := by
    rw [Finset.sum_comm]
    simp_rw [hcol]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Fintype.card_subtype]
  have hC : (Fintype.card U : ℂ) * (Fintype.card V : ℂ) = (Fintype.card Q : ℂ) := by
    rw [← hA, hB, mul_comm]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact_mod_cast hC
private theorem exists_rel_of_dvd_pairing_of_card_mul_eq {La Q P : Type} [AddCommGroup La] [AddCommGroup Q]
    [Finite Q] (N : ℕ) [NeZero N] (π : La →+ Q) (B : Q →+ Q →+ ZMod N)
    (hπeq : ∀ a a', π a = π a' → ∃ c, a' = a + N • c)
    (hL : ∀ y, (∀ x, B y x = 0) → y = 0) (hR : ∀ x, (∀ y, B y x = 0) → x = 0)
    (E : La → La → ℤ) (hE : ∀ a a', ((E a a' : ℤ) : ZMod N) = B (π a) (π a'))
    (T : Set P) (R : La → P → Prop) (hRinv : ∀ a b p, R a p → R (a + N • b) p)
    (hRfun : ∀ a p p', R a p → R a p' → p = p') (hRsurj : ∀ p, ∃ a, R a p)
    (hcard : Nat.card P * Nat.card T = Nat.card Q)
    (horth : ∀ a p a' p', R a p → p ∈ T → R a' p' → (N : ℤ) ∣ E a a')
    (a : La) (ha : ∀ a' p', R a' p' → (N : ℤ) ∣ E a a') : ∃ p, R a p := by
  classical
  have hz : ∀ a a', (N : ℤ) ∣ E a a' → B (π a) (π a') = 0 := fun a a' h => by
    rw [← hE]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  set S : Set Q := {q | ∃ a p, R a p ∧ π a = q} with hSdef
  set ST : Set Q := {q | ∃ a p, R a p ∧ p ∈ T ∧ π a = q} with hSTdef
  set U : AddSubgroup Q := AddSubgroup.closure ST with hUdef
  set V : AddSubgroup Q := ⨅ t ∈ U, (B t).ker with hVdef
  set W : AddSubgroup Q := ⨅ x ∈ V, (B.flip x).ker with hWdef
  have hmemV : ∀ x, x ∈ V ↔ ∀ t ∈ U, B t x = 0 := by
    intro x; simp [hVdef, AddSubgroup.mem_iInf]
  have hmemW : ∀ y, y ∈ W ↔ ∀ x ∈ V, B y x = 0 := by
    intro y; simp [hWdef, AddSubgroup.mem_iInf]
  have h1 : Nat.card U * Nat.card V = Nat.card Q := card_mul_card_orthogonal_eq_card_of_nondegenerate N B hL U
  have h2 : Nat.card V * Nat.card W = Nat.card Q :=
    card_mul_card_orthogonal_eq_card_of_nondegenerate N B.flip (fun x hx => hR x (fun y => by simpa using hx y)) V
  have hSV : S ⊆ (V : Set Q) := by
    rintro q ⟨a', p', hr, rfl⟩
    rw [SetLike.mem_coe, hmemV]
    intro t ht
    have hle : U ≤ (B.flip (π a')).ker := by
      rw [hUdef, AddSubgroup.closure_le]
      rintro _ ⟨a0, p0, h0, hp0, rfl⟩
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, AddMonoidHom.flip_apply]
      exact hz _ _ (horth a0 p0 a' p' h0 hp0 hr)
    simpa using hle ht
  have hSTU : ST ⊆ (U : Set Q) := AddSubgroup.subset_closure
  have hUW : U ≤ W := by
    intro t ht
    rw [hmemW]
    intro x hx
    exact (hmemV x).mp hx t ht
  have hPS : Nat.card P ≤ Nat.card S := by
    refine Nat.card_le_card_of_injective
      (fun p => ⟨π (hRsurj p).choose, (hRsurj p).choose, p, (hRsurj p).choose_spec, rfl⟩) ?_
    intro p p' h
    have h' : π (hRsurj p).choose = π (hRsurj p').choose := congrArg Subtype.val h
    obtain ⟨c, hc⟩ := hπeq _ _ h'
    have := hRinv _ c p (hRsurj p).choose_spec
    rw [← hc] at this
    exact hRfun _ _ _ this (hRsurj p').choose_spec
  have hTST : Nat.card T ≤ Nat.card ST := by
    refine Nat.card_le_card_of_injective
      (fun p : T => ⟨π (hRsurj p).choose, (hRsurj p).choose, p, (hRsurj p).choose_spec, p.2, rfl⟩) ?_
    intro p p' h
    have h' : π (hRsurj p).choose = π (hRsurj p').choose := congrArg Subtype.val h
    obtain ⟨c, hc⟩ := hπeq _ _ h'
    have := hRinv _ c p (hRsurj p).choose_spec
    rw [← hc] at this
    exact Subtype.ext (hRfun _ _ _ this (hRsurj p').choose_spec)
  have hSVc : Nat.card S ≤ Nat.card V := Nat.card_mono (Set.toFinite _) hSV
  have hSTUc : Nat.card ST ≤ Nat.card U := Nat.card_mono (Set.toFinite _) hSTU
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hPT : Nat.card P * Nat.card T ≤ Nat.card S * Nat.card ST := Nat.mul_le_mul hPS hTST
  have hTpos : 0 < Nat.card T := by
    rcases Nat.eq_zero_or_pos (Nat.card T) with h | h
    · rw [h, mul_zero] at hcard; omega
    · exact h
  have hSTpos : 0 < Nat.card ST := lt_of_lt_of_le hTpos hTST
  have hSeq : Nat.card S = Nat.card V := by
    by_contra hne
    have hlt : Nat.card S < Nat.card V := lt_of_le_of_ne hSVc hne
    have h3 : Nat.card S * Nat.card ST < Nat.card V * Nat.card U :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt hSTpos) (Nat.mul_le_mul_left _ hSTUc)
    rw [mul_comm (Nat.card V)] at h3
    omega
  have hSpos : 0 < Nat.card S := by rw [hSeq]; exact hVpos
  have hSTeq : Nat.card ST = Nat.card U := by
    by_contra hne
    have hlt : Nat.card ST < Nat.card U := lt_of_le_of_ne hSTUc hne
    have h3 : Nat.card S * Nat.card ST < Nat.card V * Nat.card U := by
      rw [hSeq]; exact Nat.mul_lt_mul_of_pos_left hlt hVpos
    rw [mul_comm (Nat.card V)] at h3
    omega
  have hSVset : S = (V : Set Q) := by
    apply Set.eq_of_subset_of_ncard_le hSV
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact hSeq.symm.le
  have hSTUset : ST = (U : Set Q) := by
    apply Set.eq_of_subset_of_ncard_le hSTU
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact hSTeq.symm.le
  have hWU : Nat.card W ≤ Nat.card U := by
    have : Nat.card V * Nat.card W = Nat.card V * Nat.card U := by rw [h2, ← h1, mul_comm]
    exact (Nat.eq_of_mul_eq_mul_left hVpos this).le
  have hUWeq : U = W := AddSubgroup.eq_of_le_of_card_ge hUW hWU
  have haW : π a ∈ W := by
    rw [hmemW]
    intro x hx
    have hxS : x ∈ S := by rw [hSVset]; exact hx
    obtain ⟨a', p', hr, rfl⟩ := hxS
    exact hz _ _ (ha a' p' hr)
  have haST : π a ∈ ST := by
    rw [hSTUset, SetLike.mem_coe, hUWeq]
    exact haW
  obtain ⟨a0, p0, h0, _, he⟩ := haST
  obtain ⟨c, hc⟩ := hπeq _ _ he
  exact ⟨p0, hc ▸ hRinv a0 c p0 h0⟩
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La), Function.Bijective EF → ∀ (N : ℕ), 0 < N → ∀ (P : Type) (T : Set P) (R : La → P → Prop), (∀ a b p, R a p → R (a + N • b) p) → (∀ a p p', R a p → R a p' → p = p') → (∀ p, ∃ a, R a p) → Nat.card P * Nat.card T = N ^ Module.finrank ℤ La → (∀ a p a' p', R a p → p ∈ T → R a' p' → (N : ℤ) ∣ EF a a') → ∀ a, (∀ a' p', R a' p' → (N : ℤ) ∣ EF a a') → ∃ p, R a p := by
  intro La _ _ _ EF hEF N hN P T R hRinv hRfun hRsurj hcard horth a ha
  classical
  have : NeZero N := ⟨hN.ne'⟩
  let b := Module.Free.chooseBasis ℤ La
  let M : Matrix (Module.Free.ChooseBasisIndex ℤ La) (Module.Free.ChooseBasisIndex ℤ La) (ZMod N) :=
    fun i j => ((EF (b i) (b j) : ℤ) : ZMod N)
  let π : La →+ (Module.Free.ChooseBasisIndex ℤ La → ZMod N) :=
    { toFun := fun a i => ((b.repr a i : ℤ) : ZMod N)
      map_zero' := by ext i; simp
      map_add' := by intro x y; ext i; simp }
  let B : (Module.Free.ChooseBasisIndex ℤ La → ZMod N) →+
      (Module.Free.ChooseBasisIndex ℤ La → ZMod N) →+ ZMod N :=
    AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun x => dotProduct (Matrix.vecMul y M) x)
      (fun x x' => dotProduct_add _ _ _))
      (fun y y' => by ext x; simp [Matrix.add_vecMul, add_dotProduct])
  have hBapp : ∀ y x, B y x = dotProduct (Matrix.vecMul y M) x := fun _ _ => rfl
  have hπapp : ∀ a i, π a i = ((b.repr a i : ℤ) : ZMod N) := fun _ _ => rfl
  have hE : ∀ a a', ((EF a a' : ℤ) : ZMod N) = B (π a) (π a') := by
    intro a a'
    have hZ : EF a a' = ∑ i, ∑ j, b.repr a i * EF (b i) (b j) * b.repr a' j := by
      calc EF a a' = EF (∑ i, b.repr a i • b i) (∑ j, b.repr a' j • b j) := by
            rw [b.sum_repr, b.sum_repr]
        _ = _ := by
            simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
              Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            ring
    rw [hZ, hBapp]
    simp only [Matrix.vecMul, dotProduct, hπapp, M, Int.cast_sum, Int.cast_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hπN : ∀ c, π ((N : ℕ) • c) = 0 := by
    intro c; ext i; simp [hπapp]
  have hdiv : ∀ a, (∀ y, B (π a) y = 0) → ∃ c, a = N • c := by
    intro a h
    apply exists_eq_nsmul_of_forall_dvd_of_bijective EF hEF N hN a
    intro x
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hE]
    exact h _
  have hsurj : ∀ y, ∃ a, π a = y := by
    intro y
    refine ⟨b.equivFun.symm (fun i => ((y i).val : ℤ)), ?_⟩
    ext i
    rw [hπapp, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp
  have hL : ∀ y, (∀ x, B y x = 0) → y = 0 := by
    intro y hy
    obtain ⟨a, rfl⟩ := hsurj y
    obtain ⟨c, rfl⟩ := hdiv a (fun x => hy x)
    exact hπN c
  have hπeq : ∀ a a', π a = π a' → ∃ c, a' = a + N • c := by
    intro a a' h
    obtain ⟨c, hc⟩ := hdiv (a' - a) (fun y => by rw [map_sub, h, sub_self, map_zero]; rfl)
    exact ⟨c, by rw [← hc]; abel⟩
  have hinj : Function.Injective (fun y => Matrix.vecMul y M) := by
    intro y y' h
    have h' : ∀ x, B (y - y') x = 0 := by
      intro x
      rw [hBapp, Matrix.sub_vecMul]
      simp only at h
      rw [h, sub_self, zero_dotProduct]
    exact sub_eq_zero.mp (hL _ h')
  have hsv : Function.Surjective (fun y => Matrix.vecMul y M) := Finite.injective_iff_surjective.mp hinj
  have hR : ∀ x, (∀ y, B y x = 0) → x = 0 := by
    intro x hx
    ext i
    obtain ⟨y, hy⟩ := hsv (Pi.single i 1)
    have := hx y
    rw [hBapp] at this
    simp only at hy
    rw [hy, single_dotProduct, one_mul] at this
    simpa using this
  have hQ : Nat.card (Module.Free.ChooseBasisIndex ℤ La → ZMod N) = N ^ Module.finrank ℤ La := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Module.finrank_eq_card_chooseBasisIndex]
  exact exists_rel_of_dvd_pairing_of_card_mul_eq N π B hπeq hL hR (fun a a' => EF a a') hE T R hRinv hRfun hRsurj
    (hcard.trans hQ.symm) horth a ha
end GlobalTheory
