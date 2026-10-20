-- Prove2me | solution 1 for MulticlassDS.Compress.lemma39_list_compression
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-19T23:28:48.344978+00:00
-- url     : https://prove2.me/submissions/844883b6-fe81-4794-8e83-0e53624879f9

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_MulticlassDS_Compress_Compression

set_option autoImplicit false

namespace L39
open MulticlassDS.Compress

variable {X Y : Type*}

/-- the labeling of the finite set `P` by `h` (`none` off `P`). -/
noncomputable def labP (P : Finset X) (h : X → Y) : X → Option Y := by
  classical exact fun x => if x ∈ P then some (h x) else none

def VP (H : Set (X → Y)) (P : Finset X) : Set (X → Option Y) := labP P '' H

noncomputable def edges (P : Finset X) (v : X → Option Y) : Finset (X × (X → Option Y)) := by
  classical exact P.image (fun p => (p, Function.update v p none))

def HallOK (H : Set (X → Y)) (P : Finset X) : Prop :=
  ∃ f : ↥(VP H P) → X × (X → Option Y), Function.Injective f ∧ ∀ v, f v ∈ edges P v.1

noncomputable def orient (H : Set (X → Y)) (P : Finset X) (hh : HallOK H P) :
    ↥(VP H P) → X × (X → Option Y) := Classical.choose hh

/-- the one-inclusion prediction at `p` on the set `P`, given the labels `g` off `p`. -/
def basePred (H : Set (X → Y)) (P : Finset X) (p : X) (g : X → Option Y) : Set Y :=
  {y | ∃ hh : HallOK H P, ∃ v : ↥(VP H P), orient H P hh v = (p, g) ∧ v.1 p = some y}

lemma basePred_encard (H : Set (X → Y)) (P : Finset X) (p : X) (g : X → Option Y) :
    (basePred H P p g).encard ≤ 1 := by
  rw [Set.encard_le_one_iff]
  rintro a b ⟨hh, v, hv, hva⟩ ⟨hh', v', hv', hvb⟩
  have hinj := (Classical.choose_spec hh).1
  have hvv : v = v' := hinj (hv.trans hv'.symm)
  subst hvv
  rw [hva] at hvb
  exact Option.some_injective _ hvb

lemma not_ds {H : Set (X → Y)} {d : ℕ} (hd : dsDim H = d) (S : Fin (d + 1) → X) :
    ¬ DSShatters H S := by
  intro hS
  have h2 : ((d + 1 : ℕ) : ℕ∞) ≤ dsDim H := by
    unfold dsDim
    exact le_iSup₂_of_le (d + 1) S (le_iSup_of_le hS le_rfl)
  rw [hd] at h2
  have : d + 1 ≤ d := by exact_mod_cast h2
  omega

lemma labP_mem {P : Finset X} {h : X → Y} {x : X} (hx : x ∈ P) : labP P h x = some (h x) := by
  classical
  unfold labP
  simp [hx]

open Classical in
lemma lonely {H : Set (X → Y)} {d : ℕ} (hd : dsDim H = d) (P : Finset X) (hP : P.card = d + 1)
    (s : Finset (X → Option Y)) (hs : ↑s ⊆ VP H P) (hne : s.Nonempty) :
    ∃ v ∈ s, ∃ p ∈ P, ∀ w ∈ s, Function.update w p none = Function.update v p none → w = v := by
  classical
  by_contra hcon
  push Not at hcon
  let S : Fin (d + 1) → X := fun i => (P.equivFin.symm (Fin.cast hP.symm i) : X)
  have hSP : ∀ i, S i ∈ P := fun i => (P.equivFin.symm (Fin.cast hP.symm i)).2
  have hSinj : Function.Injective S := by
    intro i j hij
    have := Subtype.ext hij
    have := P.equivFin.symm.injective this
    exact Fin.cast_injective _ this
  apply not_ds hd S
  refine ⟨{g | ∃ v ∈ s, ∀ i, v (S i) = some (g i)}, ?_, ?_, ?_, ?_⟩
  · rintro g ⟨v, hv, hg⟩
    obtain ⟨h, hH, rfl⟩ := hs hv
    refine ⟨h, hH, ?_⟩
    funext i
    have := hg i
    rw [labP_mem (hSP i)] at this
    exact Option.some_injective _ this
  · obtain ⟨v, hv⟩ := hne
    obtain ⟨h, hH, rfl⟩ := hs hv
    exact ⟨h ∘ S, labP P h, hv, fun i => by rw [labP_mem (hSP i)]; rfl⟩
  · have : {g : Fin (d + 1) → Y | ∃ v ∈ s, ∀ i, v (S i) = some (g i)} =
        ⋃ v ∈ s, {g : Fin (d + 1) → Y | ∀ i, v (S i) = some (g i)} := by
      ext g; simp
    rw [this]
    refine Set.Finite.biUnion s.finite_toSet (fun v _ => Set.Subsingleton.finite ?_)
    intro g1 hg1 g2 hg2
    funext i
    have h1 := hg1 i
    rw [hg2 i] at h1
    exact (Option.some_injective _ h1).symm
  · rintro g ⟨v, hv, hg⟩ i
    obtain ⟨w, hw, hupd, hwv⟩ := hcon v hv (S i) (hSP i)
    obtain ⟨h', hH', rfl⟩ := hs hw
    have hwS : ∀ j, labP P h' (S j) = some (h' (S j)) := fun j => labP_mem (hSP j)
    refine ⟨h' ∘ S, ⟨labP P h', hw, hwS⟩, ?_, ?_⟩
    · intro heq
      apply hwv
      funext x
      by_cases hx : x = S i
      · subst hx
        rw [hwS i, hg i]
        exact congrArg some heq
      · have := congrFun hupd x
        simpa [Function.update, hx] using this
    · intro j hj
      have hne' : S j ≠ S i := fun h => hj (hSinj h)
      have := congrFun hupd (S j)
      simp only [Function.update, hne', dite_false] at this
      rw [hwS j, hg j] at this
      exact Option.some_injective _ this

lemma hall_ok {H : Set (X → Y)} {d : ℕ} (hd : dsDim H = d) (P : Finset X) (hP : P.card = d + 1) :
    HallOK H P := by
  classical
  unfold HallOK
  rw [← Finset.all_card_le_biUnion_card_iff_exists_injective]
  have key : ∀ k : ℕ, ∀ s : Finset ↥(VP H P), s.card = k →
      k ≤ (s.biUnion (fun v => edges P v.1)).card := by
    intro k
    induction k with
    | zero => intro s _; exact Nat.zero_le _
    | succ k ih =>
      intro s hs
      have hne : (s.map (Function.Embedding.subtype _)).Nonempty := by
        rw [Finset.map_nonempty, ← Finset.card_pos, hs]; omega
      obtain ⟨v, hv, p, hp, hlon⟩ := lonely hd P hP (s.map (Function.Embedding.subtype _))
        (by intro x hx; simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hx
            obtain ⟨y, _, rfl⟩ := hx; exact y.2) hne
      obtain ⟨v', hv's, rfl⟩ := Finset.mem_map.mp hv
      have hcard : (s.erase v').card = k := by rw [Finset.card_erase_of_mem hv's, hs]; rfl
      have ih' := ih _ hcard
      have hsub : (s.erase v').biUnion (fun v => edges P v.1) ⊆ s.biUnion (fun v => edges P v.1) :=
        Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.erase_subset _ _)
      have hmem : (p, Function.update v'.1 p none) ∈ s.biUnion (fun v => edges P v.1) := by
        rw [Finset.mem_biUnion]
        refine ⟨v', hv's, ?_⟩
        unfold edges
        exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
      have hnot : (p, Function.update v'.1 p none) ∉ (s.erase v').biUnion (fun v => edges P v.1) := by
        rw [Finset.mem_biUnion]
        rintro ⟨w, hw, hwe⟩
        unfold edges at hwe
        obtain ⟨p', _, hpe⟩ := Finset.mem_image.mp hwe
        simp only [Prod.mk.injEq] at hpe
        obtain ⟨rfl, hpe⟩ := hpe
        have := hlon w.1 (Finset.mem_map.mpr ⟨w, Finset.mem_of_mem_erase hw, rfl⟩) hpe
        exact (Finset.ne_of_mem_erase hw) (Subtype.ext this)
      have hlt := Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨_, hmem, hnot⟩)
      omega
  intro s
  exact key _ s rfl


open Classical in
noncomputable def lab {m : ℕ} (s : Fin m → X × Y) (x : X) : Option Y :=
  if h : ∃ j, (s j).1 = x then some (s h.choose).2 else none

noncomputable def pts {m : ℕ} (s : Fin m → X × Y) : Finset X := by
  classical exact Finset.univ.image (fun j => (s j).1)

noncomputable def restr (D : Finset X) (g : X → Option Y) : X → Option Y := by
  classical exact fun q => if q ∈ D then g q else none

open Classical in
/-- the list learner on a block `s` of `d + t` examples. -/
noncomputable def Lam (H : Set (X → Y)) (d : ℕ) {m : ℕ} (s : Fin m → X × Y) (x : X) : Set Y :=
  if ∃ j, (s j).1 = x then {y | lab s x = some y}
  else ⋃ D ∈ (pts s).powersetCard d, basePred H (insert x D) x (restr D (lab s))

lemma Lam_encard (H : Set (X → Y)) {d m : ℕ} (hdm : d ≤ m) (s : Fin m → X × Y) (x : X) :
    (Lam H d s x).encard ≤ (m.choose d : ℕ∞) := by
  classical
  have hc : 1 ≤ m.choose d := Nat.choose_pos hdm
  unfold Lam
  split_ifs with h
  · calc ({y | lab s x = some y} : Set Y).encard ≤ 1 := by
          rw [Set.encard_le_one_iff]
          intro a b ha hb
          have ha' : lab s x = some a := ha
          have hb' : lab s x = some b := hb
          rw [ha'] at hb'
          exact Option.some_injective _ hb'
      _ ≤ _ := by exact_mod_cast hc
  · calc _ ≤ ∑ D ∈ (pts s).powersetCard d,
            (basePred H (insert x D) x (restr D (lab s))).encard :=
          Finset.set_encard_biUnion_le _ _
      _ ≤ ∑ D ∈ (pts s).powersetCard d, (1 : ℕ∞) :=
          Finset.sum_le_sum (fun D _ => basePred_encard _ _ _ _)
      _ = (((pts s).powersetCard d).card : ℕ∞) := by simp
      _ ≤ _ := by
          rw [Finset.card_powersetCard]
          have : (pts s).card ≤ m := by
            unfold pts; exact (Finset.card_image_le).trans (by simp)
          exact_mod_cast Nat.choose_le_choose d this

lemma lab_eq {m : ℕ} (s : Fin m → X × Y) (h : X → Y) (hs : ∀ j, h (s j).1 = (s j).2) (x : X)
    (hx : ∃ j, (s j).1 = x) : lab s x = some (h x) := by
  classical
  unfold lab
  rw [dif_pos hx]
  congr 1
  rw [← hs hx.choose, hx.choose_spec]

lemma good_of_mem (H : Set (X → Y)) (d : ℕ) {m : ℕ} (s : Fin m → X × Y) (h : X → Y)
    (hs : ∀ j, h (s j).1 = (s j).2) (x : X) (hx : ∃ j, (s j).1 = x) : h x ∈ Lam H d s x := by
  unfold Lam
  rw [if_pos hx]
  exact lab_eq s h hs x hx

open Classical in
/-- at most `d` leave-one-out mistakes on any realizable `(d+t+1)`-sequence. -/
theorem good_count (H : Set (X → Y)) {d t : ℕ} (hd : dsDim H = d) (h : X → Y) (hH : h ∈ H)
    (z : Fin (d + t + 1) → X × Y) (hz : ∀ i, h (z i).1 = (z i).2) :
    (Finset.univ.filter (fun j : Fin (d + t + 1) =>
      (z j).2 ∉ Lam H d (fun l => z (j.succAbove l)) (z j).1)).card ≤ d := by
  by_contra hc
  push Not at hc
  obtain ⟨K, hKC, hK⟩ := Finset.exists_subset_card_eq (show d + 1 ≤ _ from hc)
  have hbad : ∀ c ∈ K, (z c).2 ∉ Lam H d (fun l => z (c.succAbove l)) (z c).1 := by
    intro c hc; exact (Finset.mem_filter.mp (hKC hc)).2
  have hgood : ∀ c, (∃ j, (z (c.succAbove j)).1 = (z c).1) →
      (z c).2 ∈ Lam H d (fun l => z (c.succAbove l)) (z c).1 := by
    intro c hx
    rw [← hz c]
    exact good_of_mem H d _ h (fun j => hz _) _ hx
  by_cases hinj : Set.InjOn (fun k => (z k).1) (K : Set (Fin (d + t + 1)))
  · set P := K.image (fun k => (z k).1) with hPdef
    have hP : P.card = d + 1 := by rw [Finset.card_image_of_injOn hinj, hK]
    have hh := hall_ok (H := H) hd P hP
    let v : ↥(VP H P) := ⟨labP P h, h, hH, rfl⟩
    have hspec := (Classical.choose_spec hh).2 v
    unfold edges at hspec
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hspec
    obtain ⟨c, hcK, rfl⟩ := Finset.mem_image.mp hp
    apply hbad c hcK
    by_cases hx : ∃ j, (z (c.succAbove j)).1 = (z c).1
    · exact hgood c hx
    · unfold Lam
      rw [if_neg hx]
      rw [Set.mem_iUnion₂]
      refine ⟨P.erase (z c).1, ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        constructor
        · intro q hq
          obtain ⟨k, hkK, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hq)
          have hkc : k ≠ c := by rintro rfl; exact (Finset.ne_of_mem_erase hq) rfl
          obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hkc
          unfold pts
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
        · rw [Finset.card_erase_of_mem hp, hP]; rfl
      · rw [Finset.insert_erase hp]
        refine ⟨hh, v, ?_, ?_⟩
        · have hpe' : orient H P hh v = ((z c).1, Function.update v.1 (z c).1 none) := hpe.symm
          rw [hpe']
          congr 1
          funext q
          by_cases hq : q = (z c).1
          · rw [hq]
            simp [restr]
          · rw [Function.update_of_ne hq]
            unfold restr
            by_cases hqP : q ∈ P
            · show labP P h q = _
              rw [if_pos (Finset.mem_erase.mpr ⟨hq, hqP⟩), labP_mem hqP]
              obtain ⟨k, hkK, hkq⟩ := Finset.mem_image.mp hqP
              have hkc : k ≠ c := by rintro rfl; exact hq hkq.symm
              obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hkc
              exact (lab_eq _ h (fun l => hz _) q ⟨j, hkq⟩).symm
            · rw [if_neg (fun hm => hqP (Finset.mem_of_mem_erase hm))]
              show labP P h q = none
              unfold labP
              simp [hqP]
        · show labP P h (z c).1 = some (z c).2
          rw [labP_mem hp, hz]
  · simp only [Set.InjOn, not_forall, Finset.mem_coe] at hinj
    obtain ⟨a, haK, b, hbK, hab, hne⟩ := hinj
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq (Ne.symm hne)
    exact hbad a haK (hgood a ⟨j, by rw [hj]; exact hab.symm⟩)

lemma loo_slice {n m : ℕ} (Mis : (Fin m → Fin n) → Fin n → Prop) [∀ s i, Decidable (Mis s i)]
    (w : Fin n → ℕ) (j : Fin (m + 1)) :
    ∑ z : Fin (m + 1) → Fin n, (∏ t, w (z t)) * (if Mis (z ∘ j.succAbove) (z j) then 1 else 0) =
      ∑ s : Fin m → Fin n, (∏ t, w (s t)) * ∑ i, (if Mis s i then w i else 0) := by
  let e := Fin.insertNthEquiv (fun _ : Fin (m + 1) => Fin n) j
  rw [← e.sum_comp]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have h1 : (e (a, s)) j = a := by
    simp [e, Fin.insertNthEquiv]
  have h2 : (e (a, s)) ∘ j.succAbove = s := by
    funext t
    simp [e, Fin.insertNthEquiv]
  rw [Fin.prod_univ_succAbove _ j, h1]
  have h3 : ∀ t, (e (a, s)) (j.succAbove t) = s t := fun t => congrFun h2 t
  simp only [h3, h2]
  split_ifs <;> ring

/-- Leave-one-out averaging: if every `(m+1)`-sequence has at most `k` leave-one-out mistakes,
then for every weighting some `m`-sequence has weighted error at most `k/(m+1)`. -/
theorem loo {n m : ℕ} (Mis : (Fin m → Fin n) → Fin n → Prop) [∀ s i, Decidable (Mis s i)]
    (k : ℕ) (hn : 0 < n)
    (hk : ∀ z : Fin (m + 1) → Fin n,
      (Finset.univ.filter (fun j => Mis (z ∘ j.succAbove) (z j))).card ≤ k)
    (w : Fin n → ℕ) :
    ∃ s : Fin m → Fin n, (m + 1) * ∑ i, (if Mis s i then w i else 0) ≤ k * ∑ i, w i := by
  set P : (Fin m → Fin n) → ℕ := fun s => ∏ t, w (s t) with hP
  set E : (Fin m → Fin n) → ℕ := fun s => ∑ i, (if Mis s i then w i else 0) with hE
  have htot : ∑ z : Fin (m + 1) → Fin n, (∏ t, w (z t)) *
      (Finset.univ.filter (fun j => Mis (z ∘ j.succAbove) (z j))).card =
      (m + 1) * ∑ s, P s * E s := by
    simp only [Finset.card_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [loo_slice Mis w]
    simp [hP, hE, Finset.mul_sum]
  have hle : ∑ z : Fin (m + 1) → Fin n, (∏ t, w (z t)) *
      (Finset.univ.filter (fun j => Mis (z ∘ j.succAbove) (z j))).card ≤
      ∑ z : Fin (m + 1) → Fin n, (∏ t, w (z t)) * k :=
    Finset.sum_le_sum (fun z _ => Nat.mul_le_mul_left _ (hk z))
  have hpow : ∑ z : Fin (m + 1) → Fin n, (∏ t, w (z t)) * k = k * ((∑ i, w i) * ∑ s, P s) := by
    rw [← Finset.sum_mul, ← Fintype.sum_pow, hP, ← Fintype.sum_pow, pow_succ]
    ring
  rw [htot, hpow] at hle
  by_contra hcon
  push Not at hcon
  have hlt : ∀ s, k * ∑ i, w i < (m + 1) * E s := hcon
  rcases Nat.eq_zero_or_pos (∑ s, P s) with h0 | hpos
  · -- then the total weight is zero
    have hw : ∑ i, w i = 0 := by
      rw [hP, ← Fintype.sum_pow] at h0
      exact pow_eq_zero_iff'.mp h0 |>.1
    have hwi : ∀ i, w i = 0 := fun i =>
      (Finset.sum_eq_zero_iff.mp hw) i (Finset.mem_univ i)
    have := hlt (fun _ => ⟨0, hn⟩)
    simp [hE, hwi] at this
  · obtain ⟨s₀, -, hs₀⟩ := Finset.sum_pos_iff.mp hpos
    have hstrict : ∑ s, P s * (k * ∑ i, w i) < ∑ s, P s * ((m + 1) * E s) := by
      apply Finset.sum_lt_sum
      · intro s _
        exact Nat.mul_le_mul_left _ (hlt s).le
      · exact ⟨s₀, Finset.mem_univ _, Nat.mul_lt_mul_of_pos_left (hlt s₀) hs₀⟩
    have e1 : ∑ s, P s * (k * ∑ i, w i) = k * ((∑ i, w i) * ∑ s, P s) := by
      rw [← Finset.sum_mul]; ring
    have e2 : ∑ s, P s * ((m + 1) * E s) = (m + 1) * ∑ s, P s * E s := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
    rw [e1, e2] at hstrict
    exact absurd hle (not_le.mpr hstrict)


theorem greedy {n m : ℕ} (Mis : (Fin m → Fin n) → Fin n → Prop) [∀ s i, Decidable (Mis s i)]
    (k : ℕ) (hn : 0 < n)
    (hk : ∀ z : Fin (m + 1) → Fin n,
      (Finset.univ.filter (fun j => Mis (z ∘ j.succAbove) (z j))).card ≤ k) :
    ∀ R : ℕ, ∀ U : Finset (Fin n), ∃ B : Fin R → (Fin m → Fin n),
      (m + 1) ^ R * (U.filter (fun i => ∀ r, Mis (B r) i)).card ≤ k ^ R * U.card := by
  intro R
  induction R with
  | zero => intro U; exact ⟨Fin.elim0, by simp⟩
  | succ R ih =>
    intro U
    obtain ⟨s, hs⟩ := loo Mis k hn hk (fun i => if i ∈ U then 1 else 0)
    have e1 : ∑ i, (if Mis s i then (if i ∈ U then 1 else 0) else 0) = (U.filter (Mis s)).card := by
      have : ∀ i, (if Mis s i then (if i ∈ U then 1 else 0) else 0) =
          (if i ∈ U.filter (Mis s) then 1 else 0) := by
        intro i; simp only [Finset.mem_filter]; split_ifs <;> simp_all
      simp only [this, Finset.sum_boole]
      simp
      exact congrArg Finset.card (by ext x; simp)
    have e2 : ∑ i, (if i ∈ U then 1 else 0) = U.card := by simp
    rw [e1, e2] at hs
    obtain ⟨B', hB'⟩ := ih (U.filter (Mis s))
    refine ⟨Fin.cons s B', ?_⟩
    have hfil : U.filter (fun i => ∀ r : Fin (R + 1), Mis ((Fin.cons s B' : Fin (R + 1) → _) r) i) =
        (U.filter (Mis s)).filter (fun i => ∀ r, Mis (B' r) i) := by
      ext i; simp [Fin.forall_fin_succ, and_assoc]
    rw [hfil]
    calc (m + 1) ^ (R + 1) * ((U.filter (Mis s)).filter (fun i => ∀ r, Mis (B' r) i)).card
        = (m + 1) * ((m + 1) ^ R * ((U.filter (Mis s)).filter (fun i => ∀ r, Mis (B' r) i)).card) := by
          ring
      _ ≤ (m + 1) * (k ^ R * (U.filter (Mis s)).card) := Nat.mul_le_mul_left _ hB'
      _ = k ^ R * ((m + 1) * (U.filter (Mis s)).card) := by ring
      _ ≤ k ^ R * (k * U.card) := Nat.mul_le_mul_left _ hs
      _ = k ^ (R + 1) * U.card := by ring

lemma key_real (d t n R : ℕ) (hn : 0 < n)
    (hR : ((d : ℝ) + t + 1) / (t + 1) * Real.logb 2 (2 * (n : ℝ)) < R + 1) :
    d ^ R * n < (d + t + 1) ^ R := by
  have hN : (0 : ℝ) < d + t + 1 := by positivity
  have ht1 : (0 : ℝ) < t + 1 := by positivity
  set q : ℝ := (t + 1) / (d + t + 1) with hq
  have hq0 : 0 < q := div_pos ht1 hN
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : Real.logb 2 (2 * (n : ℝ)) = 1 + Real.logb 2 n := by
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
  have hlogn : Real.log n ≤ Real.logb 2 n := by
    rw [Real.logb]
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have hl0 : 0 ≤ Real.log n := Real.log_nonneg hnR
    rw [le_div_iff₀ h2]; nlinarith
  have hqle : q ≤ 1 := by
    rw [hq, div_le_one hN]; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hqR : Real.log n < q * R := by
    have h0 : (d + t + 1 : ℝ) / (t + 1) * Real.logb 2 (2 * n) * q = Real.logb 2 (2 * n) := by
      rw [hq]; field_simp
    have h1 : Real.logb 2 (2 * n) < (R + 1) * q := by
      rw [← h0]; exact mul_lt_mul_of_pos_right hR hq0
    rw [hL] at h1; nlinarith
  have hfac : ((d : ℝ) / (d + t + 1)) = 1 - q := by rw [hq]; field_simp; ring
  have hpow : ((d : ℝ) / (d + t + 1)) ^ R ≤ Real.exp (-(q * R)) := by
    rw [hfac]
    calc (1 - q) ^ R ≤ (Real.exp (-q)) ^ R := by
          apply pow_le_pow_left₀ (by linarith)
          have := Real.add_one_le_exp (-q); linarith
      _ = Real.exp (-(q * R)) := by rw [← Real.exp_nat_mul]; ring_nf
  have hexp : Real.exp (-(q * R)) < 1 / n := by
    rw [one_div, ← Real.exp_log (by positivity : (0 : ℝ) < n), ← Real.exp_neg]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hmain : ((d : ℝ) / (d + t + 1)) ^ R * n < 1 := by
    calc _ ≤ Real.exp (-(q * R)) * n := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ < 1 / n * n := mul_lt_mul_of_pos_right hexp (by positivity)
      _ = 1 := by field_simp
  rw [div_pow, div_mul_eq_mul_div, div_lt_one (by positivity)] at hmain
  exact_mod_cast hmain

end L39

open MulticlassDS.Compress in
theorem solution {X Y : Type*} (H : Set (X → Y)) (d : ℕ) (hd : dsDim H = d)
    (n t : ℕ) (hn : 0 < n) (ht : 0 < t) :
    ∃ r₁ p : ℕ,
      (r₁ : ℝ) ≤ ((d : ℝ) + t + 1) / (t + 1) * (d + t) * Real.logb 2 (2 * (n : ℝ)) ∧
      (p : ℝ) ≤ (Nat.choose (d + t + 1) (t + 1) : ℝ) * Real.logb 2 (2 * (n : ℝ)) ∧
      ∃ ρ : (Fin r₁ → X × Y) → X → Set Y, IsListCompressionScheme H n r₁ p ρ := by
  classical
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL0 : 0 ≤ Real.logb 2 (2 * (n : ℝ)) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hA0 : (0 : ℝ) ≤ ((d : ℝ) + t + 1) / (t + 1) * Real.logb 2 (2 * (n : ℝ)) := by positivity
  obtain ⟨R, hR⟩ : ∃ R, R = ⌊((d : ℝ) + t + 1) / (t + 1) * Real.logb 2 (2 * (n : ℝ))⌋₊ := ⟨_, rfl⟩
  have hRle : (R : ℝ) ≤ ((d : ℝ) + t + 1) / (t + 1) * Real.logb 2 (2 * (n : ℝ)) := by
    rw [hR]; exact Nat.floor_le hA0
  have hRgt : ((d : ℝ) + t + 1) / (t + 1) * Real.logb 2 (2 * (n : ℝ)) < R + 1 := by
    rw [hR]; exact Nat.lt_floor_add_one _
  have hch : ((d : ℝ) + t + 1) * ((d + t).choose t : ℕ) =
      ((d + t + 1).choose (t + 1) : ℕ) * ((t : ℝ) + 1) := by
    have := Nat.add_one_mul_choose_eq (d + t) t
    exact_mod_cast this
  refine ⟨R * (d + t), R * (d + t).choose t, ?_, ?_, ?_⟩
  · push_cast
    calc (R : ℝ) * (d + t) ≤ (((d : ℝ) + t + 1) / (t + 1) * Real.logb 2 (2 * (n : ℝ))) * (d + t) :=
          mul_le_mul_of_nonneg_right hRle (by positivity)
      _ = _ := by ring
  · rw [Nat.cast_mul]
    have ht1 : (0 : ℝ) < t + 1 := by positivity
    calc (R : ℝ) * ((d + t).choose t : ℕ)
        ≤ (((d : ℝ) + t + 1) / (t + 1) * Real.logb 2 (2 * (n : ℝ))) * ((d + t).choose t : ℕ) :=
          mul_le_mul_of_nonneg_right hRle (by positivity)
      _ = (((d : ℝ) + t + 1) * ((d + t).choose t : ℕ)) / (t + 1) * Real.logb 2 (2 * (n : ℝ)) := by
          ring
      _ = _ := by rw [hch]; field_simp
  · refine ⟨fun S' x => ⋃ r : Fin R, L39.Lam H d (fun l => S' (finProdFinEquiv (r, l))) x, ?_, ?_⟩
    · intro S' x
      calc _ ≤ ∑ r : Fin R, (L39.Lam H d (fun l => S' (finProdFinEquiv (r, l))) x).encard :=
            Set.encard_iUnion_le_of_fintype _
        _ ≤ ∑ r : Fin R, ((d + t).choose d : ℕ∞) :=
            Finset.sum_le_sum (fun r _ => L39.Lam_encard H (by omega) _ x)
        _ = ((R * (d + t).choose t : ℕ) : ℕ∞) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              Nat.choose_symm_add]
            push_cast; ring
    · intro S hS
      obtain ⟨h, hH, hreal⟩ := hS
      have hk : ∀ z : Fin (d + t + 1) → Fin n,
          (Finset.univ.filter (fun j => (fun (s : Fin (d + t) → Fin n) (i : Fin n) =>
            (S i).2 ∉ L39.Lam H d (fun l => S (s l)) (S i).1) (z ∘ j.succAbove) (z j))).card ≤ d := by
        intro z
        have := L39.good_count H hd h hH (fun i => S (z i)) (fun i => hreal (z i))
        convert this using 2
        ext j
        simp
      obtain ⟨B, hB⟩ := L39.greedy (fun (s : Fin (d + t) → Fin n) (i : Fin n) =>
            (S i).2 ∉ L39.Lam H d (fun l => S (s l)) (S i).1) d hn hk R Finset.univ
      rw [Finset.card_univ, Fintype.card_fin] at hB
      have hlt := L39.key_real d t n R hn hRgt
      have hcount : (Finset.univ.filter (fun i => ∀ r, (S i).2 ∉
          L39.Lam H d (fun l => S (B r l)) (S i).1)).card = 0 := by
        by_contra hc0
        have h1 : 1 ≤ (Finset.univ.filter (fun i => ∀ r, (S i).2 ∉
            L39.Lam H d (fun l => S (B r l)) (S i).1)).card := Nat.one_le_iff_ne_zero.mpr hc0
        have h2 := Nat.mul_le_mul_left ((d + t + 1) ^ R) h1
        have h3 : (d + t + 1) ^ R * (Finset.univ.filter (fun i => ∀ r, (S i).2 ∉
            L39.Lam H d (fun l => S (B r l)) (S i).1)).card ≤ d ^ R * n := hB
        rw [mul_one] at h2
        omega
      refine ⟨fun j => S (B (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2), ?_, ?_⟩
      · intro j; exact ⟨_, rfl⟩
      · intro i
        have hi : i ∉ Finset.univ.filter (fun i => ∀ r, (S i).2 ∉
            L39.Lam H d (fun l => S (B r l)) (S i).1) := by
          rw [Finset.card_eq_zero.mp hcount]; simp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hi
        obtain ⟨r, hr⟩ := hi
        rw [Set.mem_iUnion]
        refine ⟨r, ?_⟩
        simpa using hr
